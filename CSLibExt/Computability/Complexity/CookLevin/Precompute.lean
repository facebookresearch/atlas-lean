/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Pre.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Pre.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib); the certificate bound generalized from `n ^ k` to a polynomial
`k : Polynomial ℕ`, computed by a new Horner loop (`horner_run`, `hornVal_coeffs`) that replaces the
power loop in `cprog`; module docstring rewritten for this repository (the source's notes and status
lines dropped), missing docstrings added, long lines wrapped.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import CSLibExt.Computability.Complexity.CookLevin.Assembly

/-!
# Cook-Levin: the precomputation, composed with the assembled generator

The reduction machine receives only the raw input `s : List (Fin r)`. Everything else is a constant
of the program: the raw-symbol map `ι` and separator `sep` (so `x = s.map ι ++ [sep]`), the
certificate bound `k : Polynomial ℕ` (`m = |s| + 1 + k(|s|)`), the time constants `c, e`
(`T = (m + c)^e`) and `d = depth M` (`H = capH m T d`).

* Counter-view additions: `decS_*`, the multi-target transfer `xferS`, the power loop `pow_run`,
  and Horner evaluation `horner_run` of a polynomial on counters (`hornVal_coeffs`). The source
  computed `n + 1 + n ^ k` for a fixed exponent; formal-math's `NP` allows an arbitrary polynomial
  certificate bound, so the bound is evaluated by Horner's rule here.
* `cprog` and `cprog_run`: the counter program loading the twelve generator counters.
* The full machine: stacks and labels, the two embeddings, the read loop `rdT`/`read_run`.
* `fprog` and `pre_run`: the read loop and the counter program reach exactly
  `Assembly.real_run`'s preloads.
* `full_run`: raw input to `encodeCNF (Phi …)` with no hypotheses; `fullTM` as a `FinTM2`.
* `IsPoly` and `fullB_poly`, `full_time_poly`: one polynomial bounds every run.
-/

@[expose] public section



namespace Cslib.Complexity.CookLevin.Precompute

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Turing Function
open Cslib.Complexity.CookLevin.CounterView (SK SΓ st st_c st_out update_st_c update_st_nil emitS
  incS drainS copyS mulS mulS_run bud_st MS)

/-! ## [LIB] Counter-view additions: decrement, multi-target transfer, the power loop -/

section CLib

variable {C : Type} [DecidableEq C] {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem decS_pos {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) {j : ℕ} (hx : F x = j + 1) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x j) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := j) (by simp [hx])
  rw [update_st_c] at this
  exact this

theorem decS_zero {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) (hx : F x = 0) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifZero, false, st F o⟩ :=
  decr_run_zero hp v (by simp [hx])

/-- **Unit targets of a multi-target transfer.** For a list $y_1, \dots, y_j$ of counters, the list
of transfer targets that pushes one unit on each counter $y_i$, in the same order. -/
def tg (ys : List C) : List (Σ k, SΓ C k) := ys.map fun y => ⟨.c y, ()⟩

omit [DecidableEq C] in
theorem tg_keys (ys : List C) : (tg ys).keys = ys.map SK.c := by
  simp [tg, List.keys]

omit [DecidableEq C] in
theorem tg_nodupKeys {ys : List C} (h : ys.Nodup) : (tg ys).NodupKeys := by
  unfold List.NodupKeys
  rw [tg_keys]
  exact h.map (fun _ _ h => by cases h; rfl)

theorem dlookup_tg (ys : List C) (z : C) :
    List.dlookup (SK.c z) (tg ys) = if z ∈ ys then some () else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : z = y
      · subst h; simp [tg, List.dlookup_cons_eq]
      · rw [tg, List.map_cons, List.dlookup_cons_ne _ _ (by simpa using h)]
        rw [← tg, ih]; simp [h]

theorem dlookup_tg_out (ys : List C) : List.dlookup (SK.out) (tg ys) = none := by
  rw [List.dlookup_eq_none, tg_keys]; simp

/-- **Counters after a multi-target transfer.** Given counter values $F : C \to \mathbb{N}$, a
counter $x \in C$ and a list $Y$ of counters, the counter values after transferring $x$ to $Y$
form the function that sends $x$ to $0$, sends every $z \ne x$ occurring in $Y$ to
$F(z) + F(x)$, and sends every other $z$ to $F(z)$. -/
def xf (F : C → ℕ) (x : C) (ys : List C) : C → ℕ :=
  fun z => if z = x then 0 else if z ∈ ys then F z + F x else F z

/-- **Multi-target transfer.** Let $M$ be a counter machine with counters indexed by $C$, a
Boolean output stack and a Boolean state, let $x \in C$, and let $Y$ be a list of distinct
counters not containing $x$. Suppose the instruction at label $\ell$ is the transfer loop that
pops counter $x$ and pushes one unit on every counter of $Y$, returning to $\ell$ while $x$ is
nonempty and continuing at label $\ell'$ once it is empty. Then for all counter values
$F : C \to \mathbb{N}$, every state bit $v$ and every output stack $o$, the machine runs in
exactly $F(x) + 1$ steps from label $\ell$ with state $v$, counter values $F$ and output stack $o$
to label $\ell'$ with state false, output stack $o$ and the counter values after transferring
$x$ to $Y$: counter $x$ becomes $0$, each counter of $Y$ gains $F(x)$, and every other counter
keeps its value. -/
theorem xferS {self next : Λ} {x : C} {ys : List C} (hp : M self = xfer (.c x) (tg ys) self next)
    (hnd : ys.Nodup) (hx : x ∉ ys) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (xf F x ys) o⟩ := by
  have := xfer_run hp (tg_nodupKeys hnd) (by rw [tg_keys]; simpa using hx) () (F x) v (st F o) rfl
  have e : addU (tg ys) (F x) (update (st F o) (SK.c x) []) = st (xf F x ys) o := by
    funext k
    rcases k with _ | z
    · simp [addU, dlookup_tg_out]
    · simp only [addU, dlookup_tg]
      by_cases hz : z = x
      · subst hz; simp [xf, hx]
      · rw [update_of_ne (by simpa using hz)]
        by_cases hy : z ∈ ys
        · simp [xf, hz, hy, add_comm]
        · simp [xf, hz, hy]
  rw [e] at this
  exact this

/-- **Stages of the power loop.** The labels of one power-loop site: a head stage, a
multiplication stage $\mathrm{mul}(s)$ for each stage $s$ of a multiplication site, a drain stage
and a move stage. -/
inductive PW
  | hd
  | mul (s : MS)
  | drn
  | mv
  deriving DecidableEq, Fintype

/-- **Power-loop program.** Given six counters $b$, $k$, $p$, $q$, $a$, $t$, a label for each
power-loop stage and an exit label, the power loop is the following program on the stages. At
the head stage it pops one unit from $k$; if $k$ was empty it goes to the exit label, otherwise
to the first multiplication stage. The multiplication stages add $p \cdot b$ to $q$ (a
multiplication site with index counter $a$ and scratch counter $t$) and then go to the drain
stage. The drain stage empties $p$ and goes to the move stage. The move stage moves the contents
of $q$ onto $p$ and returns to the head stage.

When the six counters are distinct and $q = a = t = 0$ at the start, each round multiplies $p$ by
$b$, so the loop replaces $p$ by $p \cdot b^k$ and ends with $k = 0$. -/
def powS (b kc p q ad t : C) (mk : PW → Λ) (exit : Λ) : PW → TM2.Stmt (SΓ C) Λ Bool
  | .hd => decr (.c kc) exit (mk (.mul .head))
  | .mul s => mulS p ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c p) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [p]) (mk .mv) (mk .hd)

/-- **Step budget of the power loop.** For natural numbers $j$ (the number of rounds), $p$ (the
start value) and $b$ (the base), the step budget of the power loop is
$j \, (p \, (b + 1)^j \, (3 b + 5) + 5) + 1$. -/
def powB (j p b : ℕ) : ℕ := j * (p * (b + 1) ^ j * (3 * b + 5) + 5) + 1

/-- **The power loop.** Let $b, k, p, q, a, t$ be pairwise distinct counters of a counter machine
$M$, let $\mu$ assign a label to each power-loop stage and let $\nu$ be a label. Suppose that for
every power-loop stage $s$ the label $\mu(s)$ runs the power-loop program for $b, k, p, q, a, t$
with stage labels $\mu$ and exit label $\nu$ at stage $s$. Let $j \in \mathbb{N}$, let $F$ be
counter values with $F(k) = j$ and $F(q) = F(a) = F(t) = 0$, let $v$ be a flag and $o$ an
output. Then $M$ runs from the head stage $\mu(\mathrm{hd})$ with flag $v$, counters $F$ and
output $o$ to the label $\nu$ with flag false, output $o$, and counters $F$ except that $p$ holds
$F(p) \cdot F(b)^j$ and $k$ holds $0$, within $j\,(F(p)\,(F(b) + 1)^j\,(3F(b) + 5) + 5) + 1$
steps, the step budget of the power loop for $j$ rounds, start value $F(p)$ and base $F(b)$. -/
theorem pow_run {b kc p q ad t : C} {mk : PW → Λ} {exit : Λ}
    (hp : ∀ s, M (mk s) = powS b kc p q ad t mk exit s)
    (hnd : [b, kc, p, q, ad, t].Nodup) :
    ∀ (j : ℕ) (F : C → ℕ), F kc = j → F q = 0 → F ad = 0 → F t = 0 → ∀ (v : Bool) (o : List Bool),
      RunLe M (powB j (F p) (F b)) ⟨some (mk .hd), v, st F o⟩
        ⟨some exit, false, st (update (update F p (F p * F b ^ j)) kc 0) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hbk, hbp, hbq, hbad, hbt⟩, ⟨hkp, hkq, hkad, hkt⟩, ⟨hpq, hpad, hpt⟩, ⟨hqad, hqt⟩,
    hadt, -⟩ := hnd
  intro j
  induction j with
  | zero =>
      intro F hk hq had ht v o
      have r := decS_zero (hp .hd) F hk v o
      have hF : update (update F p (F p * F b ^ 0)) kc 0 = F := by
        funext z; by_cases h1 : z = kc
        · subst h1; simp [hk]
        · by_cases h2 : z = p
          · subst h2; simp [h1]
          · simp [h1]
      rw [hF]; exact r.le (by simp [powB])
  | succ j ih =>
      intro F hk hq had ht v o
      -- decrement
      have r1 := decS_pos (hp .hd) F hk v o
      set F1 := update F kc j with hF1
      -- q += p * b
      have r2 := mulS_run (a := p) (ad := ad) (b := b) (c := q) (t := t)
        (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
        (by simp [hpad, (Ne.symm hbp), hpq, hpt, (Ne.symm hbad), (Ne.symm hqad), hadt, hbq, hbt,
            hqt])
        F1 (by simp [hF1, (Ne.symm hkad), had]) (by simp [hF1, (Ne.symm hkt), ht]) true o
      set F2 := update F1 q (F1 p * F1 b + F1 q) with hF2
      -- drain p
      have r3 := drainS (hp .drn) F2 false o
      set F3 := update F2 p 0 with hF3
      -- move q to p
      have r4 := xferS (hp .mv) (by simp) (by simpa using (Ne.symm hpq)) F3 false o
      set F4 := xf F3 q [p] with hF4
      have hF1p : F1 p = F p := by rw [hF1, update_of_ne (Ne.symm hkp)]
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hbk]
      have hF1q : F1 q = 0 := by rw [hF1, update_of_ne (Ne.symm hkq), hq]
      have hF2p : F2 p = F p := by rw [hF2, update_of_ne hpq, hF1p]
      have hF3q : F3 q = F p * F b := by
        rw [hF3, update_of_ne (Ne.symm hpq), hF2, update_self, hF1p, hF1b, hF1q, add_zero]
      have hrest : ∀ z, z ≠ q → z ≠ p → z ≠ kc → F4 z = F z := by
        intro z h1 h2 h3
        simp only [hF4, xf, ite_eq_right h1, List.mem_singleton, ite_eq_right h2, hF3, hF2, hF1,
          update_of_ne h1, update_of_ne h2, update_of_ne h3]
      have h4p : F4 p = F p * F b := by
        simp only [hF4, xf, ite_eq_right hpq, List.mem_singleton, ite_true, hF3, update_self,
            zero_add]
        exact hF3q
      have h4k : F4 kc = j := by
        simp only [hF4, xf, ite_eq_right hkq, List.mem_singleton, ite_eq_right hkp, hF3, hF2, hF1,
          update_of_ne hkp, update_of_ne hkq, update_self]
      have h4b : F4 b = F b := hrest b hbq hbp hbk
      have r5 := ih F4 h4k (by simp [hF4, xf])
        (by rw [hrest ad (Ne.symm hqad) (Ne.symm hpad) (Ne.symm hkad), had])
        (by rw [hrest t (Ne.symm hqt) (Ne.symm hpt) (Ne.symm hkt), ht]) false o
      have hend : update (update F4 p (F4 p * F4 b ^ j)) kc 0 =
          update (update F p (F p * F b ^ (j + 1))) kc 0 := by
        funext z
        by_cases h1 : z = kc
        · subst h1; simp
        rw [update_of_ne h1, update_of_ne h1]
        by_cases h2 : z = p
        · subst h2; rw [update_self, update_self, h4p, h4b, pow_succ]; ring
        rw [update_of_ne h2, update_of_ne h2]
        by_cases h3 : z = q
        · subst h3; simp [hF4, xf, hq]
        exact hrest z h3 h2 h1
      rw [hend, h4p, h4b] at r5
      rw [hF2p] at r3
      rw [hF3q] at r4
      rw [hF1p, hF1b] at r2
      have := ((((r1.le le_rfl).trans (r2.le le_rfl)).trans (r3.le le_rfl)).trans
        (r4.le le_rfl)).trans r5
      refine this.mono ?_
      unfold powB
      have hpw : F p * F b * (F b + 1) ^ j ≤ F p * (F b + 1) ^ (j + 1) := by
        rw [pow_succ, mul_assoc, mul_comm (F b)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
      have hp1 : F p ≤ F p * (F b + 1) ^ (j + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))
      have h1 := Nat.mul_le_mul_right (3 * F b + 5) hp1
      have h2 := Nat.mul_le_mul_left j (Nat.add_le_add_right
        (Nat.mul_le_mul_right (3 * F b + 5) hpw) 5)
      nlinarith [h1, h2]


/-! ### Horner evaluation of a polynomial on counters

Not in the source repository: it computes `m = n + 1 + p(n)` for formal-math's arbitrary
polynomial certificate bound `p`, where the source computed `n + 1 + n ^ k`. -/

/-- **Stages of a Horner round.** The Horner-round stages are $\mathsf{mul}(s)$, one for each
stage $s$ of a multiplication site, and the three stages $\mathsf{drn}$, $\mathsf{mv}$ and
$\mathsf{add}$. In a Horner round they label the multiplication, draining the accumulator,
moving the product into the accumulator, and adding the coefficient. -/
inductive HW
  | mul (s : MS)
  | drn
  | mv
  | add
  deriving DecidableEq, Fintype

/-- **The statements of one Horner round.** For counters $b, \mathit{acc}, q, d, t$, a number
$a \in \mathbb{N}$, stage labels $\mu$ and an exit label $\nu$: the statements performing
$\mathit{acc} \leftarrow \mathit{acc} \cdot b + a$ in four stages, each stage reaching the next
through $\mu$. The multiplication stages add $\mathit{acc} \cdot b$ to $q$ (with index counter $d$
and scratch counter $t$), then the drain stage empties $\mathit{acc}$, the move stage transfers
$q$ into $\mathit{acc}$, and the add stage pushes $a$ units onto $\mathit{acc}$ and continues at
$\nu$. -/
def hornS (b acc q ad t : C) (a : ℕ) (mk : HW → Λ) (next : Λ) : HW → TM2.Stmt (SΓ C) Λ Bool
  | .mul s => mulS acc ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c acc) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [acc]) (mk .mv) (mk .add)
  | .add => emitR (.c acc) (List.replicate a ()) next

/-- **Step count of one Horner round.** For an accumulator value $A$ and a base $b$, the number
$A(2b + 3) + A + 2 + (A + 1) + (Ab + 1) + 1$: the exact number of steps one Horner round takes
from $\mathit{acc} = A$ with base $b$. -/
def hornStep (A b : ℕ) : ℕ := A * (2 * b + 3) + A + 2 + (A + 1) + (A * b + 1) + 1

/-- **One Horner round.** Let $b, \mathit{acc}, q, d, t$ be pairwise distinct counters of a
counter machine $M$, let $a \in \mathbb{N}$, let $\mu$ assign a label to each Horner-round stage
and let $\nu$ be a label. Suppose that for every Horner-round stage $s$ the label $\mu(s)$ runs
the Horner-round statement for $b, \mathit{acc}, q, d, t, a$ with stage labels $\mu$ and exit
label $\nu$ at stage $s$. Let $F$ be counter values with $F(q) = F(d) = F(t) = 0$, let $v$ be a
flag and $o$ an output, and let $h$ be the step count of one Horner round. Then $M$ runs from the
first multiplication stage $\mu(\mathrm{mul\ head})$ with flag $v$, counters $F$ and output $o$
in exactly $h(F(\mathit{acc}), F(b))$ steps to the label $\nu$ with flag false, output $o$, and
counters $F$ except that $\mathit{acc}$ holds $F(\mathit{acc}) \cdot F(b) + a$. -/
theorem horn_round {b acc q ad t : C} {a : ℕ} {mk : HW → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = hornS b acc q ad t a mk next s)
    (hnd : [b, acc, q, ad, t].Nodup) (F : C → ℕ) (hq : F q = 0) (had : F ad = 0)
    (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (hornStep (F acc) (F b)) ⟨some (mk (.mul .head)), v, st F o⟩
      ⟨some next, false, st (update F acc (F acc * F b + a)) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hba, hbq, hbad, hbt⟩, ⟨haq, haad, hat⟩, ⟨hqad, hqt⟩, hadt, -⟩ := hnd
  have r1 := mulS_run (a := acc) (ad := ad) (b := b) (c := q) (t := t)
    (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
    (by simp [haad, Ne.symm hba, haq, hat, Ne.symm hbad, Ne.symm hqad, hadt, hbq, hbt, hqt])
    F had ht v o
  set F1 := update F q (F acc * F b + F q) with hF1
  have r2 := drainS (hp .drn) F1 false o
  set F2 := update F1 acc 0 with hF2
  have r3 := xferS (hp .mv) (by simp) (by simpa using Ne.symm haq) F2 false o
  set F3 := xf F2 q [acc] with hF3
  have r4 := emitS (n := a) (hp .add) F3 false o
  have hF1a : F1 acc = F acc := by rw [hF1, update_of_ne haq]
  have hF2q : F2 q = F acc * F b := by
    rw [hF2, update_of_ne (Ne.symm haq), hF1, update_self, hq, add_zero]
  have hF3a : F3 acc = F acc * F b := by
    simp only [hF3, xf, ite_eq_right haq, List.mem_singleton, ite_true, hF2, update_self,
      zero_add]
    exact hF2q
  have hend : update F3 acc (a + F3 acc) = update F acc (F acc * F b + a) := by
    funext z
    by_cases h1 : z = acc
    · subst h1; rw [update_self, update_self, hF3a, add_comm]
    rw [update_of_ne h1, update_of_ne h1]
    by_cases h2 : z = q
    · subst h2; simp [hF3, xf, hq]
    simp only [hF3, xf, ite_eq_right h2, List.mem_singleton, ite_eq_right h1, hF2, hF1,
      update_of_ne h1, update_of_ne h2]
  rw [hend] at r4
  rw [hF1a] at r2
  rw [hF2q] at r3
  exact (r1.trans (r2.trans (r3.trans r4))).of_eq (by unfold hornStep; ring)

/-- **Horner value.** For a list $c_1, \dots, c_\ell$ of natural numbers and natural numbers $b$
and $A$, the Horner value of $c_1, \dots, c_\ell$ with base $b$ from accumulator $A$ is the number
obtained from the starting value $x = A$ by replacing $x$ by $x b + c_i$ for $i = 1, \dots, \ell$
in turn; for the empty list it is $A$. -/
def hornVal (cs : List ℕ) (b A : ℕ) : ℕ := cs.foldl (fun A a => A * b + a) A

/-- **Step count of the Horner rounds.** For a list $cs$ of coefficients, a base $b$ and an
accumulator value $A$: $0$ if $cs$ is empty, and if $cs$ is $a$ followed by $cs'$, the step count
$h(A, b)$ of one Horner round from $A$ with base $b$ plus the step count of $cs'$ with base $b$
from accumulator $A b + a$. This is the exact number of steps of the Horner rounds. -/
def hornT : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | a :: cs, b, A => hornStep A b + hornT cs b (A * b + a)

/-- **Horner rounds.** Let $b, \mathit{acc}, q, d, t$ be pairwise distinct counters of a counter
machine $M$, let $c_0, \dots, c_{\ell-1}$ be natural numbers, let $\mu$ assign a label
$\mu(i, s)$ to each $i \in \mathbb{N}$ and each Horner-round stage $s$, and let $\nu$ be a label.
Suppose that for every $i < \ell$ and every stage $s$ the label $\mu(i, s)$ runs, at stage $s$,
the statement of one Horner round for $b, \mathit{acc}, q, d, t$ and the number $c_i$, with
stage labels $\mu(i, \cdot)$ and exit label $\mu(i + 1, \mathrm{mul\ head})$ if $i + 1 < \ell$
and $\nu$ otherwise. Then for all $i, j \in \mathbb{N}$ with $i + j = \ell$, all counter values
$F$ with $F(q) = F(d) = F(t) = 0$, every flag $v$ and every output $o$, there is a flag $v'$ such
that $M$ runs in exactly $h$ steps from the label $\mu(i, \mathrm{mul\ head})$ if $i < \ell$ and
$\nu$ otherwise, with flag $v$, counters $F$ and output $o$, to the label $\nu$ with flag $v'$,
output $o$, and counters $F$ except that $\mathit{acc}$ holds the Horner value of
$c_i, \dots, c_{\ell-1}$ with base $F(b)$ from accumulator $F(\mathit{acc})$. Here $h$ is the
step count of the Horner rounds over $c_i, \dots, c_{\ell-1}$ with base $F(b)$ from accumulator
$F(\mathit{acc})$. -/
theorem horner_run {b acc q ad t : C} (cs : List ℕ) {mk : ℕ → HW → Λ} {exit : Λ}
    (hp : ∀ i (hi : i < cs.length) s, M (mk i s) = hornS b acc q ad t cs[i] (mk i)
      (if i + 1 < cs.length then mk (i + 1) (.mul .head) else exit) s)
    (hnd : [b, acc, q, ad, t].Nodup) :
    ∀ (j i : ℕ), i + j = cs.length → ∀ (F : C → ℕ), F q = 0 → F ad = 0 → F t = 0 →
      ∀ (v : Bool) (o : List Bool),
      ∃ v' : Bool, Run M (hornT (cs.drop i) (F b) (F acc))
        ⟨some (if i < cs.length then mk i (.mul .head) else exit), v, st F o⟩
        ⟨some exit, v', st (update F acc (hornVal (cs.drop i) (F b) (F acc))) o⟩ := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hba, hbq, hbad, hbt⟩, ⟨haq, haad, hat⟩, ⟨hqad, hqt⟩, hadt, -⟩ := hnd'
  intro j
  induction j with
  | zero =>
      intro i hi F _ _ _ v o
      have hd : cs.drop i = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨v, ?_⟩
      rw [hd, ite_eq_right (by omega)]
      simp only [hornT, hornVal, List.foldl_nil, update_eq_self]
      exact TM2Program.Run.zero _
  | succ j ih =>
      intro i hi F hq had ht v o
      have hlt : i < cs.length := by omega
      have hd : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      have r1 := horn_round (a := cs[i]) (mk := mk i) (hp i hlt) hnd F hq had ht v o
      set F1 := update F acc (F acc * F b + cs[i]) with hF1
      obtain ⟨v', r2⟩ := ih (i + 1) (by omega) F1 (by rw [hF1, update_of_ne (Ne.symm haq), hq])
        (by rw [hF1, update_of_ne (Ne.symm haad), had])
        (by rw [hF1, update_of_ne (Ne.symm hat), ht]) false o
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hba]
      have hF1a : F1 acc = F acc * F b + cs[i] := by rw [hF1, update_self]
      rw [hF1b, hF1a] at r2
      have hupd : update F1 acc (hornVal (cs.drop (i + 1)) (F b) (F acc * F b + cs[i])) =
          update F acc (hornVal (cs.drop (i + 1)) (F b) (F acc * F b + cs[i])) := by
        rw [hF1, update_idem]
      rw [hupd] at r2
      refine ⟨v', ?_⟩
      rw [ite_eq_left hlt, hd]
      exact r1.trans r2

/-- **Splitting off the starting accumulator in Horner evaluation.** For a list
$c_1, \dots, c_\ell$ of natural numbers and natural numbers $b$ and $A$, write $h(x)$ for the
Horner value of $c_1, \dots, c_\ell$ with base $b$ from accumulator $x$: the number obtained
from the starting value $x$ by replacing the current value $y$ by $y b + c_i$ for
$i = 1, \dots, \ell$ in turn. Then $h(A) = A b^{\ell} + h(0)$. -/
theorem hornVal_eq (cs : List ℕ) (b A : ℕ) :
    hornVal cs b A = A * b ^ cs.length + hornVal cs b 0 := by
  induction cs generalizing A with
  | nil => simp [hornVal]
  | cons a cs ih =>
      simp only [hornVal, List.foldl_cons, List.length_cons] at ih ⊢
      rw [ih (A * b + a), ih (0 * b + a)]
      ring

/-- **Coefficient list of a polynomial.** For a polynomial $p$ with natural-number coefficients
and natural degree $d$ (where $d = 0$ when $p = 0$), the coefficient list of $p$ is
$[p_d, p_{d-1}, \dots, p_1, p_0]$, where $p_i$ is the coefficient of $X^i$ in $p$. -/
noncomputable def coeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree + 1)).reverse.map p.coeff

theorem hornVal_range (f : ℕ → ℕ) (b D : ℕ) :
    hornVal ((List.range D).reverse.map f) b 0 = ∑ i ∈ Finset.range D, f i * b ^ i := by
  induction D with
  | zero => simp [hornVal]
  | succ D ih =>
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, Finset.sum_range_succ]
      have := hornVal_eq ((List.range D).reverse.map f) b (0 * b + f D)
      simp only [hornVal, List.foldl_cons, List.length_map, List.length_reverse,
        List.length_range] at this ih ⊢
      rw [this, ih]
      ring

/-- **Horner's rule.** For every polynomial $p$ with natural coefficients and every
$b \in \mathbb{N}$, running Horner rounds with base $b$ on the coefficients of $p$ (highest degree
first), starting from accumulator $0$, yields $p(b)$. -/
theorem hornVal_coeffs (p : Polynomial ℕ) (b : ℕ) : hornVal (coeffs p) b 0 = p.eval b := by
  rw [coeffs, hornVal_range, Polynomial.eval_eq_sum_range]


end CLib

/-! ## [CNT] The precomputation's counter program -/

/-- **Scratch counters of the counter program.** The type of the twelve private counters of the
precomputation's counter program, with constructors $N$, $P$, $Q$, $AD$, $TMP$, $KC$, $Mc$, $B$,
$Tc$, $Fx$, $Dd$, $Hc$. -/
inductive PS
  | N | P | Q | AD | TMP | KC | Mc | B | Tc | Fx | Dd | Hc
  deriving DecidableEq
instance PS.instFintypeEnumFix : Fintype PS where
  elems := ⟨↑[PS.N, PS.P, PS.Q, PS.AD, PS.TMP, PS.KC, PS.Mc, PS.B, PS.Tc, PS.Fx, PS.Dd, PS.Hc],
      by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Target counters of the counter program.** The type of the twelve counters that the
precomputation's counter program loads for the host, with constructors $uT$, $uH$, $sT$, $sH$,
$hT$, $hH$, $aT$, $aH$, $iT$, $iX$, $iE$, $iF$.

They hold the twelve preloads of the assembled generator's run. -/
inductive PT
  | uT | uH | sT | sH | hT | hH | aT | aH | iT | iX | iE | iF
  deriving DecidableEq
instance PT.instFintypeEnumFix : Fintype PT where
  elems := ⟨↑[PT.uT, PT.uH, PT.sT, PT.sH, PT.hT, PT.hH, PT.aT, PT.aH, PT.iT, PT.iX, PT.iE, PT.iF],
      by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Counters of the counter program.** A counter of the counter program is either a scratch
counter $s(x)$, for one of the twelve scratch counter names $x$, or a target counter $t(y)$, for
one of the twelve target counter names $y$: the counters are the disjoint union of the scratch
counters and the target counters. -/
inductive CC
  | s (x : PS)
  | t (y : PT)
  deriving DecidableEq, Fintype

/-- **Labels of the counter program.** For $D \in \mathbb{N}$, the number of Horner rounds, the
labels of the counter program are $p_1$; a label $\mathrm{hr}(i, s)$ for each round $i < D$ and
each Horner-round stage $s$; the labels $x_1, x_2, x_3, x_4, c_1, c_2, x_6, x_7, x_8$; a label
$w_2(s)$ for each power-loop stage $s$; $x_9$; a label $\mathrm{ml}(s)$ for each stage $s$ of a
multiplication site; the labels $x_{10}, x_{11}, x_{12}, x_{13}, x_{14}$; and
$\mathrm{done}$. -/
inductive PL (D : ℕ)
  | p1 | hr (i : Fin D) (s : HW) | x1 | x2 | x3 | x4 | c1 | c2 | x6 | x7 | x8 | w2 (s : PW) | x9
  | ml (s : MS) | x10 | x11 | x12 | x13 | x14 | done
  deriving DecidableEq, Fintype

/-- **Horner-round labels indexed by natural numbers.** For a number $D$ of Horner rounds,
$i \in \mathbb{N}$ and a Horner-round stage $s$: the counter-program label for stage $s$ of
Horner round $i$ if $i < D$, and otherwise the label $x_1$ that follows the Horner rounds.

Indices $i \ge D$ are never reached. -/
def hlab {D : ℕ} (i : ℕ) (s : HW) : PL D := if h : i < D then .hr ⟨i, h⟩ s else .x1

open CC PS PT in
/-- **The counter program.** For a polynomial $k$ with natural-number coefficients, whose
coefficient list $\kappa_0, \dots, \kappa_{D-1}$ has length $D$, and $c, e, d \in \mathbb{N}$,
the counter program is the program with the labels of the counter program for $D$ Horner rounds
that acts on a Boolean output stack and on the scratch and target counters of the counter
program as follows. It runs $D$ Horner rounds, round $i$ with coefficient $\kappa_i$, base $N$,
accumulator $P$, product counter $Q$, index counter $AD$ and scratch counter $TMP$. It moves $P$
onto both $Mc$ and the target $iE$, moves $N$ onto both $Mc$ and the target $iX$, and adds one
unit to each of $Mc$ and $iX$. It adds $Mc$ to $B$, restoring $Mc$ through $TMP$, adds $c$ units
to $B$, $e$ units to $KC$ and one unit to $Tc$, and runs the power loop with base $B$, round
counter $KC$, accumulator $Tc$, product counter $Q$, index counter $AD$ and scratch counter
$TMP$. It adds $d$ units to $Dd$, adds $Dd \cdot Tc$ to $Fx$ (index counter $AD$, scratch
counter $TMP$) and adds $d + 1$ more units to $Fx$. It moves $Fx$ onto both $Hc$ and the target
$iF$ and moves $Mc$ onto $Hc$. Finally it moves $Tc$ onto each of the targets
$uT, sT, hT, aT, iT$, moves $Hc$ onto each of the targets $uH, sH, hH, aH$, and halts.

Started with $n$ on $N$ and every other counter empty, the program computes $P = k(n)$ by
Horner's rule, $m = n + 1 + k(n)$ on $Mc$, $T = (m + c)^e$ on $Tc$, $dT + d + 1$ on $Fx$ and
$m + dT + d + 1$ on $Hc$, and so loads the twelve target counters. -/
noncomputable def cprog (k : Polynomial ℕ) (c e d : ℕ) :
    PL (coeffs k).length → TM2.Stmt (SΓ CC) (PL (coeffs k).length) Bool
  | .p1 => emitR (.c (s P)) (List.replicate 0 ()) (if 0 < (coeffs k).length then hlab 0 (.mul .head) else .x1)
  | .hr i q => hornS (s N) (s P) (s Q) (s AD) (s TMP) (coeffs k)[i] (hlab i.1)
      (if i.1 + 1 < (coeffs k).length then hlab (i.1 + 1) (.mul .head) else .x1) q
  | .x1 => xfer (.c (s P)) (tg [s Mc, t iE]) .x1 .x2
  | .x2 => xfer (.c (s N)) (tg [s Mc, t iX]) .x2 .x3
  | .x3 => emitR (.c (s Mc)) (List.replicate 1 ()) .x4
  | .x4 => emitR (.c (t iX)) (List.replicate 1 ()) .c1
  | .c1 => xfer (.c (s Mc)) [⟨.c (s B), ()⟩, ⟨.c (s TMP), ()⟩] .c1 .c2
  | .c2 => xfer (.c (s TMP)) [⟨.c (s Mc), ()⟩] .c2 .x6
  | .x6 => emitR (.c (s B)) (List.replicate c ()) .x7
  | .x7 => emitR (.c (s KC)) (List.replicate e ()) .x8
  | .x8 => emitR (.c (s Tc)) (List.replicate 1 ()) (.w2 .hd)
  | .w2 q => powS (s B) (s KC) (s Tc) (s Q) (s AD) (s TMP) PL.w2 .x9 q
  | .x9 => emitR (.c (s Dd)) (List.replicate d ()) (.ml .head)
  | .ml q => mulS (s Dd) (s AD) (s Tc) (s Fx) (s TMP) PL.ml .x10 q
  | .x10 => emitR (.c (s Fx)) (List.replicate (d + 1) ()) .x11
  | .x11 => xfer (.c (s Fx)) (tg [s Hc, t iF]) .x11 .x12
  | .x12 => xfer (.c (s Mc)) (tg [s Hc]) .x12 .x13
  | .x13 => xfer (.c (s Tc)) (tg [t uT, t sT, t hT, t aT, t iT]) .x13 .x14
  | .x14 => xfer (.c (s Hc)) (tg [t uH, t sH, t hH, t aH]) .x14 .done
  | .done => .halt

/-- **Total length bound.** For a polynomial $k$ with natural-number coefficients and
$n \in \mathbb{N}$, the total length bound is $m = n + 1 + k(n)$.

So a word $x$ of length $n + 1$ followed by a word $y$ has length at most $m$ exactly when $y$
has length at most $k(n)$. -/
def mOf (k : Polynomial ℕ) (n : ℕ) : ℕ := n + 1 + k.eval n

/-- **The precomputed time bound.** For a polynomial $k$ with natural coefficients and
$c, e, n \in \mathbb{N}$, the time bound is $T = (m + c)^e$, where $m = n + 1 + k(n)$. -/
def TOf (k : Polynomial ℕ) (c e n : ℕ) : ℕ := (mOf k n + c) ^ e

/-- **Start counter values.** For a natural number $n$, the start counter values of the counter
program give the scratch counter $N$ the value $n$ and every other counter the value $0$. -/
def F0 (n : ℕ) : CC → ℕ
  | .s .N => n
  | _ => 0

/-- **Counter values after the Horner loop.** For a polynomial $k$ with natural-number
coefficients and $n \in \mathbb{N}$, this is the assignment of values to the counters of the
counter program that gives the scratch counter $N$ the value $n$, the scratch counter $P$ the
value $k(n)$, and every other counter the value $0$.

The counter program reaches these values after its Horner loop has evaluated $k(n)$. -/
def F1 (k : Polynomial ℕ) (n : ℕ) : CC → ℕ
  | .s .N => n
  | .s .P => k.eval n
  | _ => 0

/-- **Counter values before the power loop.** For a polynomial $k$ with natural-number
coefficients and $c, e, n \in \mathbb{N}$, write $m = n + 1 + k(n)$. This is the assignment of
values to the counters of the counter program that gives the scratch counters $\mathit{Mc}$,
$B$, $\mathit{KC}$ and $\mathit{Tc}$ the values $m$, $m + c$, $e$ and $1$, the target counters
$\mathit{iX}$ and $\mathit{iE}$ the values $n + 1$ and $k(n)$, and every other counter the value
$0$. -/
def F2 (k : Polynomial ℕ) (c e n : ℕ) : CC → ℕ
  | .s .Mc => mOf k n
  | .s .B => mOf k n + c
  | .s .KC => e
  | .s .Tc => 1
  | .t .iX => n + 1
  | .t .iE => k.eval n
  | _ => 0

/-- **Counter values after the power loop.** For a polynomial $k$ with natural-number
coefficients and $c, e, n \in \mathbb{N}$, write $m = n + 1 + k(n)$. This is the assignment of
values to the counters of the counter program that gives the scratch counters $\mathit{Mc}$,
$B$ and $\mathit{Tc}$ the values $m$, $m + c$ and $(m + c)^e$, the target counters $\mathit{iX}$
and $\mathit{iE}$ the values $n + 1$ and $k(n)$, and every other counter the value $0$. -/
def F3 (k : Polynomial ℕ) (c e n : ℕ) : CC → ℕ
  | .s .Mc => mOf k n
  | .s .B => mOf k n + c
  | .s .Tc => TOf k c e n
  | .t .iX => n + 1
  | .t .iE => k.eval n
  | _ => 0

/-- **Target counter values.** For a polynomial $k$ with natural-number coefficients and natural
numbers $c, e, d, n$, let $m = n + 1 + k(n)$, $T = (m + c)^e$ and let $H = m + (T + 1)d + 1$ be
the stack cap. The target values on the twelve target counters assign $T$ to each of
$u_T, s_T, h_T, a_T, i_T$, assign $H$ to each of $u_H, s_H, h_H, a_H$, and assign $n + 1$ to
$i_X$, $k(n)$ to $i_E$ and $(T + 1)d + 1$ to $i_F$.

In particular the value at $i_F$ is $H - m$. -/
def tv (k : Polynomial ℕ) (c e d n : ℕ) : PT → ℕ
  | .uT | .sT | .hT | .aT | .iT => TOf k c e n
  | .uH | .sH | .hH | .aH => Situation.capH (mOf k n) (TOf k c e n) d
  | .iX => n + 1
  | .iE => k.eval n
  | .iF => (TOf k c e n + 1) * d + 1

/-- **Counter values at the end of the counter program.** For a polynomial $k$ with
natural-number coefficients and $c, e, d, n \in \mathbb{N}$, write $m = n + 1 + k(n)$ and
$T = (m + c)^e$. This is the assignment of values to the counters of the counter program that
gives the scratch counters $B$ and $\mathit{Dd}$ the values $m + c$ and $d$, gives each target
counter its target value ($T$ for $\mathit{uT}$, $\mathit{sT}$, $\mathit{hT}$, $\mathit{aT}$ and
$\mathit{iT}$; $m + (T + 1)d + 1$ for $\mathit{uH}$, $\mathit{sH}$, $\mathit{hH}$ and
$\mathit{aH}$; $n + 1$ for $\mathit{iX}$; $k(n)$ for $\mathit{iE}$; $(T + 1)d + 1$ for
$\mathit{iF}$), and gives every other scratch counter the value $0$. -/
def F4 (k : Polynomial ℕ) (c e d n : ℕ) : CC → ℕ
  | .s .B => mOf k n + c
  | .s .Dd => d
  | .t y => tv k c e d n y
  | _ => 0

/-- **Step budget of the counter program.** For a polynomial $k$ with natural-number coefficients
and natural numbers $c, e, d, n$, let $m = n + 1 + k(n)$, $T = (m + c)^e$ and
$H = m + (T + 1)d + 1$. The step budget of the counter program at $(k, c, e, d, n)$ is
$$
1 + h + (k(n) + 1) + (n + 1) + 2 + (2m + 2) + 3 + p + 1 + (d(2T + 3) + d + 2) + 1 +
(dT + d + 2) + (m + 1) + (T + 1) + (H + 1),
$$
where $h$ is the exact step count of the Horner rounds over the coefficient list of $k$ with
base $n$ from accumulator $0$, and $p = e\left((m + c + 1)^e (3(m + c) + 5) + 5\right) + 1$ is
the step budget of the power loop with $e$ rounds, start value $1$ and base $m + c$. -/
noncomputable def cB (k : Polynomial ℕ) (c e d n : ℕ) : ℕ :=
  1 + hornT (coeffs k) n 0 + (k.eval n + 1) + (n + 1) + 2 + (2 * mOf k n + 2) + 3 + powB e 1 (mOf k n + c) +
    1 + (d * (2 * TOf k c e n + 3) + d + 2) + 1 + (d * TOf k c e n + d + 2) + (mOf k n + 1) +
    (TOf k c e n + 1) + (Situation.capH (mOf k n) (TOf k c e n) d + 1)

open CC PS PT in
/-- **The counter program's run.** Let $k$ be a polynomial with natural-number coefficients, let
$c, e, d, n$ be natural numbers, and put $m = n + 1 + k(n)$ and $T = (m + c)^e$. Start the
counter program for $k, c, e, d$ at its first label with any flag, any output stack $o$, the
scratch counter $N$ equal to $n$ and every other counter equal to $0$. Then, in a number of
steps at most the step budget of the counter program at $(k, c, e, d, n)$, it reaches its label
$\mathrm{done}$ with flag false, output stack $o$, and counter values $T$ on the targets
$uT, sT, hT, aT, iT$; $m + (T + 1)d + 1$ on the targets $uH, sH, hH, aH$; $n + 1$ on $iX$;
$k(n)$ on $iE$; $(T + 1)d + 1$ on $iF$; $m + c$ on the scratch counter $B$; $d$ on the scratch
counter $Dd$; and $0$ on every other counter. -/
theorem cprog_run (k : Polynomial ℕ) (c e d n : ℕ) (v : Bool) (o : List Bool) :
    RunLe (cprog k c e d) (cB k c e d n) ⟨some .p1, v, st (F0 n) o⟩
      ⟨some .done, false, st (F4 k c e d n) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := cprog k c e d) (self := .p1) rfl _ _ _).bud ?_
  obtain ⟨vh, rh⟩ := horner_run (M := cprog k c e d) (b := s N) (acc := s P) (q := s Q)
    (ad := s AD) (t := s TMP) (coeffs k) (mk := hlab) (exit := .x1)
    (fun i hi q => by rw [show hlab i q = PL.hr ⟨i, hi⟩ q from dif_pos hi]; rfl) (by decide)
    (coeffs k).length 0 (by omega)
    (update (F0 n) (s P) (0 + F0 n (s P))) (by simp [F0]) (by simp [F0]) (by simp [F0]) v o
  rw [List.drop_zero] at rh
  refine rh.bud ?_
  refine bud_st (F' := F1 k n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [F0, F1, hornVal_coeffs]) ?_
  refine (xferS (M := cprog k c e d) (self := .x1) (next := .x2) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x2) (next := .x3) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x3) (next := .x4) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x4) (next := .c1) rfl _ _ _).bud ?_
  refine (copyS (M := cprog k c e d) (l₁ := .c1) (l₂ := .c2) (next := .x6) rfl rfl (by decide)
    (by decide) (by decide) _ (by simp [xf, F1]) _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x6) (next := .x7) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x7) (next := .x8) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x8) (next := .w2 .hd) rfl _ _ _).bud ?_
  refine bud_st (F' := F2 k c e n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [xf, F1, F2, mOf] <;> omega) ?_
  refine (pow_run (M := cprog k c e d) (mk := PL.w2) (exit := .x9) (fun _ => rfl) (by decide) e _
    (by simp [F2]) (by simp [F2]) (by simp [F2]) (by simp [F2]) _ _).bud ?_
  refine bud_st (F' := F3 k c e n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [F2, F3, TOf]) ?_
  refine (emitS (M := cprog k c e d) (self := .x9) (next := .ml .head) rfl _ _ _).bud ?_
  refine (mulS_run (M := cprog k c e d) (mk := PL.ml) (next := .x10) (fun _ => rfl) (by decide) _
    (by simp [F3]) (by simp [F3]) _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x10) (next := .x11) rfl _ _ _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x11) (next := .x12) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x12) (next := .x13) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x13) (next := .x14) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x14) (next := .done) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [xf, F0, F1, F2, F3, cB, Situation.capH, mOf]
    generalize TOf k c e n = T
    linarith
  · congr 2
    funext z; rcases z with z | z <;> cases z <;> simp [xf, F3, F4, tv, Situation.capH] <;> ring


/-! ## [FULL] The full machine: read loop, counter program, host -/

open Cslib.Complexity.CookLevin.Assembly

/-- **Stacks of the full machine.** The full machine has one stack for each host stack, one
stack for the raw input, and one stack for each scratch counter of the counter program. -/
inductive FK
  | h (k : HK)
  | raw
  | pc (x : PS)
  deriving DecidableEq, Fintype

/-- **Alphabets of the full machine.** For natural numbers $g, r$, the alphabet of a stack of the
full machine is the host's alphabet with $g$ input codes on each host stack,
$\{0, 1, \dots, r - 1\}$ on the raw input stack, and the one-point type on each private
counter. -/
abbrev FΓ (g r : ℕ) : FK → Type
  | .h k => HΓ g k
  | .raw => Fin r
  | .pc _ => Unit

/-- **Labels of the full machine.** For $D \in \mathbb{N}$ and a type $\Lambda$ of host labels,
the labels of the full machine are the read-loop label, one label for each label of the counter
program with $D$ Horner rounds, and one label for each element of $\Lambda$. -/
inductive FL (D : ℕ) (Λ : Type)
  | rd
  | pre (l : PL D)
  | h (l : Λ)
  deriving DecidableEq, Fintype

/-- **Host counter of each target.** The map from the twelve targets to host stacks: $uT$ and $uH$
go to the counters $T_n$ and $H_s$ of the update generator's block, $sT$ and $sH$ to those of the
situation-definition generator's block, $hT$ and $hH$ to those of the shift generator's block,
$aT$ and $aH$ to those of the accept generator's block, and $iT$, $iX$, $iE$, $iF$ to the counters
$T_n$, $X_n$, $E_n$, $F_n$ of the init generator's block. -/
def tgt : PT → HK
  | .uT => .up .Tn
  | .uH => .up .Hs
  | .sT => .sd .Tn
  | .sH => .sd .Hs
  | .hT => .sh .Tn
  | .hH => .sh .Hs
  | .aT => .ac .Tn
  | .aH => .ac .Hs
  | .iT => .ini .Tn
  | .iX => .ini .Xn
  | .iE => .ini .En
  | .iF => .ini .Fn

/-- **Stack renaming of the counter program.** The stack renaming of the counter program into the
full machine sends the output stack to the host's output stack, each scratch counter $x$ to the
full machine's private counter for $x$, and each target counter $y$ to the host counter that
receives $y$. -/
def eC : SK CC → FK
  | .out => .h .out
  | .c (.s x) => .pc x
  | .c (.t y) => .h (tgt y)

section Embs

variable (g r : ℕ)

/-- **Embedding of the counter program's stacks.** For natural numbers $g, r$, the stack embedding
of the counter program into the full machine with $g$ input codes and $r$ raw input symbols
renames stacks by the stack renaming of the counter program and identifies the alphabet of each
stack with that of its image by the identity (Booleans on the output stack, the one-point type
on each counter). -/
def embC : SEmb (SΓ CC) (FΓ g r) where
  e := eC
  inj := by
    intro a b h
    rcases a with _ | (x | y) <;> rcases b with _ | (x' | y') <;>
      simp only [eC, FK.h.injEq, FK.pc.injEq, reduceCtorEq] at h ⊢
    all_goals first
      | exact h
      | (subst h; rfl)
      | (cases y <;> cases h)
      | (cases y' <;> cases h)
      | (cases y <;> cases y' <;> first | rfl | cases h)
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c (.s _) => Equiv.refl _
    | .c (.t y) => match y with
      | .uT | .uH | .sT | .sH | .hT | .hH | .aT | .aH | .iT | .iX | .iE | .iF => Equiv.refl _

/-- **Embedding of the host's stacks.** For natural numbers $g, r$, the stack embedding of the
host into the full machine with $g$ input codes and $r$ raw input symbols sends each host stack
to the same host stack of the full machine and identifies their alphabets by the identity. -/
def embH : SEmb (HΓ g) (FΓ g r) where
  e := FK.h
  inj := fun _ _ h => by cases h; rfl
  ι := fun _ => Equiv.refl _

end Embs

section Read

variable {g r D : ℕ} {Λ : Type}

/-- **The read loop.** Given a code map $c_f$ from the raw alphabet $\mathrm{Fin}\,r$ to the code
alphabet $\mathrm{Fin}\,g$, a separator code $c_s$ and a list $L$ of raw symbols, the read-loop
statement tests the symbols $i$ of $L$ in order against the top of the raw input stack. At the
first $i$ found on top, it pops it, pushes $c_f(i)$ on the host input stack and one unit on the
scratch counter $N$, and goes back to the read-loop label (with the flag true). If no symbol of
$L$ is on top, in particular when the raw input is empty, it pushes $c_s$ on the input stack, sets
the flag to false and goes to the first label of the counter program.

The full program takes $L$ to be all of $\mathrm{Fin}\,r$, so each step reads one input symbol. -/
def rdT (cf : Fin r → Fin g) (cs : Fin g) : List (Fin r) → TM2.Stmt (FΓ g r) (FL D Λ) Bool
  | [] => .push (.h .inp) (fun _ => cs) (.load (fun _ => false) (.goto fun _ => .pre .p1))
  | i :: L => .peek .raw (fun _ o => decide (o = some i))
      (.branch id (.pop .raw (fun v _ => v) (.push (.h .inp) (fun _ => cf i)
        (.push (.pc .N) (fun _ => ()) (.goto fun _ => .rd)))) (rdT cf cs L))

/-- **Stacks during the read loop.** For a list $s$ of raw symbols in $\mathrm{Fin}\,r$, a list
$w$ of input codes in $\mathrm{Fin}\,g$, $n \in \mathbb{N}$ and a list $o$ of booleans, these are
the stack contents of the full machine in which the raw-input stack holds $s$, the host input
stack holds $w$, the host output stack holds $o$, the scratch counter $N$ holds $n$ units, and
every other stack is empty.

During the read loop, $s$ is the unread rest of the input and $w$ holds the codes read so far. -/
def fst (s : List (Fin r)) (ins : List (Fin g)) (n : ℕ) (o : List Bool) : ∀ k, List (FΓ g r k)
  | .raw => s
  | .h .inp => ins
  | .h .out => o
  | .pc .N => cnt () n
  | _ => []

theorem rdT_hit (cf : Fin r → Fin g) (cs : Fin g) (a : Fin r) (s : List (Fin r))
    (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    ∀ (L : List (Fin r)), a ∈ L → ∀ v : Bool,
      TM2.stepAux (rdT (D := D) (Λ := Λ) cf cs L) v (fst (a :: s) ins n o) =
        ⟨some .rd, true, fst s (cf a :: ins) (n + 1) o⟩ := by
  intro L
  induction L with
  | nil => intro h; cases h
  | cons i L ih =>
      intro h v
      by_cases hi : a = i
      · subst hi
        simp only [rdT, TM2.stepAux]
        simp only [fst, List.head?_cons, decide_true, id, Bool.cond_true, List.tail_cons]
        congr 1
        funext k
        rcases k with k | _ | x
        · cases k <;> simp [fst]
        · simp [fst]
        · cases x <;> simp [fst, cnt_succ]
      · have hL : a ∈ L := by
          rcases List.mem_cons.1 h with h | h
          · exact absurd h hi
          · exact h
        simp only [rdT, TM2.stepAux]
        simp only [fst, List.head?_cons, Option.some.injEq, hi, decide_false, id, Bool.cond_false]
        exact ih hL false

theorem rdT_nil (cf : Fin r → Fin g) (cs : Fin g) (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    ∀ (L : List (Fin r)) (v : Bool),
      TM2.stepAux (rdT (D := D) (Λ := Λ) cf cs L) v (fst [] ins n o) =
        ⟨some (.pre .p1), false, fst [] (cs :: ins) n o⟩ := by
  intro L
  induction L with
  | nil =>
      intro v
      simp only [rdT, TM2.stepAux]
      congr 1
      funext k
      rcases k with k | _ | x
      · cases k <;> simp [fst]
      · simp [fst]
      · cases x <;> simp [fst]
  | cons i L ih =>
      intro v
      simp only [rdT, TM2.stepAux]
      simp only [fst, List.head?_nil, reduceCtorEq, decide_false, id, Bool.cond_false]
      exact ih false

/-- **The read loop's run.** Let $M$ be a program of the full machine whose read-loop label carries
the read loop over all of $\mathrm{Fin}\,r$, with code map $c_f$ and separator code $c_s$, and let
$o$ be a list of booleans. For every raw input $s = s_1 \cdots s_\ell$, list of codes $w$,
$n \in \mathbb{N}$ and flag $v$: started at the read-loop label with flag $v$, raw input stack $s$,
input stack $w$, scratch counter $N = n$, output stack $o$ and every other stack empty, $M$ runs in
exactly $\ell + 1$ steps to the counter program's first label, with flag false, raw input stack
empty, input stack $c_s, c_f(s_\ell), \dots, c_f(s_1)$ followed by $w$, scratch counter
$N = n + \ell$, output stack $o$ and every other stack empty. -/
theorem read_run {M : FL D Λ → TM2.Stmt (FΓ g r) (FL D Λ) Bool} {cf : Fin r → Fin g} {cs : Fin g}
    (hM : M .rd = rdT cf cs (List.finRange r)) (o : List Bool) :
    ∀ (s : List (Fin r)) (ins : List (Fin g)) (n : ℕ) (v : Bool),
      Run M (s.length + 1) ⟨some .rd, v, fst s ins n o⟩
        ⟨some (.pre .p1), false, fst [] (cs :: ((s.map cf).reverse ++ ins)) (n + s.length) o⟩ := by
  intro s
  induction s with
  | nil =>
      intro ins n v
      refine Run.single ?_
      simp [hM, rdT_nil]
  | cons a s ih =>
      intro ins n v
      have := ih (cf a :: ins) (n + 1) true
      rw [show (s.map cf).reverse ++ cf a :: ins = ((a :: s).map cf).reverse ++ ins by simp,
        show n + 1 + s.length = n + (a :: s).length by simp; omega] at this
      refine Run.head ?_ this
      simp only [TM2.step, hM, rdT_hit cf cs a s ins n o _ (List.mem_finRange a)]

end Read


/-! ## [COMP] The full program and its run -/

section Comp

variable {g r : ℕ} {Λ : Type}

/-- **The full program.** Let $\gamma : \mathrm{Fin}\,r \to \mathrm{Fin}\,g$ code the raw
symbols, let $\sigma \in \mathrm{Fin}\,g$ be a separator code, let $k$ be a polynomial with
natural-number coefficients, let $c, e, d \in \mathbb{N}$, and let $h$ be a host program with
labels $\Lambda$ and start label $\lambda_0 \in \Lambda$. The full program, whose counter-program
labels have $D$ Horner rounds for $D$ the length of the coefficient list of $k$, runs at the
read-loop label the read loop for $\gamma$ and $\sigma$ over all raw symbols; at a
counter-program label $l$ other than the final one, the counter program for $k, c, e, d$ at $l$,
embedded with its scratch counters on the full machine's private counters, its target counters on
the corresponding host counters and its output on the host output; at the final counter-program
label, a step that sets the state to false and jumps to the host label $\lambda_0$; and at a host
label $l$, the statement $h(l)$ on the host stacks. -/
noncomputable def fprog (cf : Fin r → Fin g) (cs : Fin g) (k : Polynomial ℕ) (c e d : ℕ) (hp : Λ → TM2.Stmt (HΓ g) Λ Bool)
    (start : Λ) : FL (coeffs k).length Λ → TM2.Stmt (FΓ g r) (FL (coeffs k).length Λ) Bool
  | .rd => rdT cf cs (List.finRange r)
  | .pre l => if l = .done then .load (fun _ => false) (.goto fun _ => .h start)
      else mapS (embC g r) FL.pre (cprog k c e d l)
  | .h l => mapS (embH g r) FL.h (hp l)

variable {cf : Fin r → Fin g} {cs : Fin g} {k : Polynomial ℕ} {c e d : ℕ} {hp : Λ → TM2.Stmt (HΓ g) Λ Bool}
  {start : Λ}

theorem embeds_C : Embeds (embC g r) FL.pre (cprog k c e d) (fprog cf cs k c e d hp start) := by
  intro l
  by_cases hl : l = .done
  · exact Or.inr (by subst hl; rfl)
  · exact Or.inl (by simp only [fprog, ite_eq_right hl])

theorem embeds_H : Embeds (embH g r) FL.h hp (fprog cf cs k c e d hp start) :=
  fun _ => Or.inl rfl

theorem agree_C (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    Agree (embC g r) (st (F0 n) o) (fst [] ins n o) := by
  intro k
  rcases k with _ | (x | y)
  · exact (List.map_id _).symm
  · cases x <;> exact (List.map_id _).symm
  · cases y <;> exact (List.map_id _).symm

theorem eC_ne_inp (k : SK CC) : eC k ≠ .h .inp := by
  rcases k with _ | (x | y) <;> simp [eC]
  cases y <;> simp [tgt]

/-- **The precomputation.** Fix the full program built from a code map $c_f$ from the raw alphabet
$\mathrm{Fin}\,r$ to the code alphabet $\mathrm{Fin}\,g$, a separator code $c_s$, a polynomial $k$
with natural coefficients, constants $c, e, d \in \mathbb{N}$, a host program and its start label.
Let $s = s_1 \cdots s_n$ be a raw input word and $o$ a list of booleans. Started at the read-loop
label with flag false, raw input stack $s$, output stack $o$ and every other stack empty, the full
program reaches the host's start label with flag false within $n + 1 + B + 1$ steps, where $B$ is
the counter program's step budget for $k, c, e, d$ at $n$. The stacks it reaches satisfy: the
output stack is still $o$; the input stack is $c_s, c_f(s_n), \dots, c_f(s_1)$; for every target
$y$, the host counter receiving $y$ has length equal to the target value of $y$ for $k, c, e, d$
at $n$; and every host stack other than the output stack, the input stack and the host counters
receiving targets is empty.

These are the preloads that the assembled generator's run expects. -/
theorem pre_run (s : List (Fin r)) (o : List Bool) :
    ∃ S : ∀ k, List (FΓ g r k),
      RunLe (fprog cf cs k c e d hp start) (s.length + 1 + cB k c e d s.length + 1)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h start), false, S⟩ ∧
      S (.h .out) = o ∧ S (.h .inp) = cs :: (s.map cf).reverse ∧
      (∀ y, (S (.h (tgt y))).length = tv k c e d s.length y) ∧
      (∀ hk, (∀ y, tgt y ≠ hk) → hk ≠ .out → hk ≠ .inp → S (.h hk) = []) := by
  have r1 := read_run (M := fprog cf cs k c e d hp start) rfl o s [] 0 false
  rw [List.append_nil, Nat.zero_add] at r1
  obtain ⟨T1, r2, a2, f2⟩ := runLe_embed (E := embC g r) FL.pre embeds_C
    (cprog_run k c e d s.length false o) (agree_C _ _ o)
  have r3 : Run (fprog cf cs k c e d hp start) 1 ⟨some (.pre .done), false, T1⟩
      ⟨some (.h start), false, T1⟩ :=
    Run.single (by simp [fprog, TM2.stepAux])
  refine ⟨T1, ((r1.le le_rfl).trans r2).trans (r3.le le_rfl), (a2 .out).trans (List.map_id _),
    ?_, fun y => by
      have := congrArg List.length (a2 (.c (.t y)))
      rw [List.length_map] at this
      exact this.trans (by simp [F4]), fun hk h1 h2 h3 => ?_⟩
  · exact (f2 _ eC_ne_inp).trans rfl
  · rw [f2 _ (fun k => by
      rcases k with _ | (x | y)
      · exact fun h => h2 (FK.h.inj h).symm
      · simp [embC, eC]
      · exact fun h => h1 y (FK.h.inj h))]
    cases hk with
    | out => exact absurd rfl h2
    | inp => exact absurd rfl h3
    | _ => rfl

end Comp


/-! ## [REAL] The full machine on the real generators: raw input to emitted formula -/

section Real

open Cslib.Complexity.CookLevin.Situation

variable {r : ℕ} {M : FinTM2} (E : Enc M)

/-- **The full program on the real generators.** For an encoding $E$ of a machine $M$, a list
$Y$ of symbols of the input stack alphabet of $M$, a symbol $a$ of the output stack alphabet of
$M$, a map $\iota$ from the raw symbols $\mathrm{Fin}\,r$ to input stack symbols of $M$, an input
stack symbol $\sigma$ of $M$ (the separator), a polynomial $k$ with natural-number coefficients
and $c, e \in \mathbb{N}$, this is the full program in which each raw symbol $i$ is coded by the
code of $\iota(i)$ under $E$, the separator code is the code of $\sigma$ under $E$,
$d = \operatorname{depth} M$, the host program is the host running the real generators of $M$
for $Y$ and $a$, and the host starts at the start label of its initial-row generator. -/
noncomputable abbrev fullProg (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) :=
  fprog (fun i => InitFamily.encF E (ι i)) (InitFamily.encF E sep) k c e (depth M) (realProg E Ys acc)
    (.ini (.pre1 .eg))

/-- **Step bound of the full machine.** For an encoding $E$ of a machine $M$, a list $Y$ of
symbols of the input stack alphabet of $M$, a polynomial $k$ with natural-number coefficients and
$c, e, n \in \mathbb{N}$, write $m = n + 1 + k(n)$ and $T = (m + c)^e$. The bound is
$n + 1 + C + 1 + R$, where $C$ is the step budget of the counter program for $k$, $c$, $e$,
$d = \operatorname{depth} M$ and $n$, and $R$ is the host's step bound for $E$ and $Y$ at $m$
and $T$.

It bounds the number of steps of the full machine on a raw input of length $n$. -/
noncomputable def fullB (Ys : List (M.Γ M.k₀)) (k : Polynomial ℕ) (c e n : ℕ) : ℕ :=
  n + 1 + cB k c e (depth M) n + 1 + realB E Ys (mOf k n) (TOf k c e n)

theorem cnt_of_len {l : List Unit} {n : ℕ} (h : l.length = n) : l = cnt () n :=
  List.eq_replicate_iff.2 ⟨h, fun _ _ => rfl⟩

/-- **The composed machine, raw input to formula.** From the raw input `s` (all other stacks
empty, output `o`), the full machine halts its host part at `fin` within `fullB` steps, having
prepended exactly `encodeCNF (Phi …)` for `x = s.map ι ++ [sep]`, `m = |s| + 1 + k(|s|)`,
`T = (m + c)^e`. **No hypotheses** (`|x| ≤ m` is discharged here). -/
theorem full_run (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (FΓ E.layout.g r k)),
      RunLe (fullProg E Ys acc ι sep k c e) (fullB E Ys k c e s.length)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h .fin), v, S⟩ ∧
      S (.h .out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
        (TOf k c e s.length)) ++ o := by
  obtain ⟨T1, r1, ho, hin, ht, hz⟩ := pre_run (cf := fun i => InitFamily.encF E (ι i))
    (cs := InitFamily.encF E sep) (k := k) (c := c) (e := e) (d := depth M) (hp := realProg E Ys acc)
    (start := .ini (.pre1 .eg)) s o
  have e1 : (s.map ι ++ [sep]).length = s.length + 1 := by simp
  have hx : (s.map ι ++ [sep]).length ≤ mOf k s.length := by rw [e1, mOf]; omega
  have e2 : mOf k s.length - (s.length + 1) = k.eval s.length := by rw [mOf]; omega
  have e3 : capH (mOf k s.length) (TOf k c e s.length) (depth M) - mOf k s.length =
      (TOf k c e s.length + 1) * depth M + 1 := by unfold capH; omega
  have nt : ∀ hk : HK, (∀ y, tgt y ≠ hk) → hk ≠ .out → hk ≠ .inp →
      T1 (.h hk) = [] := hz
  obtain ⟨v, S, hr, hout⟩ := real_run E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
    (TOf k c e s.length) hx (fun hk => T1 (.h hk)) o ho
    (hin.trans (by simp [List.map_append, List.reverse_append]))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .uT)
      case Hs => exact cnt_of_len (ht .uH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .sT)
      case Hs => exact cnt_of_len (ht .sH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .hT)
      case Hs => exact cnt_of_len (ht .hH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .aT)
      case Hs => exact cnt_of_len (ht .aH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      rw [e1, e2, e3]
      cases z
      case Tn => exact cnt_of_len (ht .iT)
      case Xn => exact cnt_of_len (ht .iX)
      case En => exact cnt_of_len (ht .iE)
      case Fn => exact cnt_of_len (ht .iF)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
  obtain ⟨T2, r2, a2, -⟩ := runLe_embed (E := embH E.layout.g r) FL.h embeds_H hr
    (S' := T1) (fun _ => (List.map_id _).symm)
  exact ⟨v, T2, r1.trans r2, ((a2 .out).trans (List.map_id _)).trans hout⟩

/-- **The full machine as a finite multi-stack Turing machine.** Given $r \in \mathbb{N}$, an
encoding $E$ of the machine $M$, a list $Y_s$ of input symbols of $M$, an output symbol $a$ of
$M$, a map $\iota$ from $\{0, \dots, r - 1\}$ to input symbols of $M$, an input symbol $\sigma$ of
$M$ (the separator), a polynomial $k$ with natural coefficients and $c, e \in \mathbb{N}$: the
finite multi-stack machine whose stacks are the full stacks (the host's stacks, the raw input
stack and the scratch counters) with the full alphabets, whose labels are the full labels, with
start label the read label, internal states the booleans with initial state false, and program
the full program built from these data. Its input stack is the raw input stack and its output
stack is the host's output stack. -/
noncomputable def fullTM (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : FinTM2 where
  K := FK
  k₀ := .raw
  k₁ := .h .out
  Γ := FΓ E.layout.g r
  Λ := FL _ _
  main := .rd
  σ := Bool
  initialState := false
  m := fullProg E Ys acc ι sep k c e

/-- **Initial configuration of the full machine.** Let $E$ be encoding data for a finite
multi-stack Turing machine $M$, and let $r$ be a natural number. Fix a list $Y$ of input-stack
symbols of $M$, an output-stack symbol $a$ of $M$, a map $\iota$ from $\{0, \dots, r-1\}$ to
input-stack symbols of $M$, a separator input-stack symbol $\sigma$ of $M$, a polynomial $k$ with
natural-number coefficients and natural numbers $c$ and $e$. On every raw input $s$, a word over
$\{0, \dots, r-1\}$, the initial configuration of the full machine built from these data is at
the read-loop label with internal state false, its raw-input stack holds $s$, and all its other
stacks (the code stack, the output stack, the scratch counters and the remaining host stacks)
are empty. -/
theorem initList_full (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) :
    initList (fullTM E Ys acc ι sep k c e) s = ⟨some .rd, false, fst s [] 0 []⟩ := by
  simp only [initList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · cases x <;> rfl

end Real

/-! ## [POLY] The step bound is a polynomial in `|s|` -/

/-- **Polynomial functions on the naturals.** A function $f : \mathbb{N} \to \mathbb{N}$ is
polynomial when there is a polynomial $p$ with natural-number coefficients such that
$f(n) = p(n)$ for every $n \in \mathbb{N}$. -/
def IsPoly (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n

namespace IsPoly

theorem const (a : ℕ) : IsPoly fun _ => a := ⟨Polynomial.C a, fun _ => by simp⟩

theorem id : IsPoly fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n + g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p + q, fun n => by simp [hp, hq]⟩

theorem mul {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n * g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p * q, fun n => by simp [hp, hq]⟩

theorem pow {f : ℕ → ℕ} (hf : IsPoly f) (j : ℕ) : IsPoly fun n => f n ^ j := by
  obtain ⟨p, hp⟩ := hf; exact ⟨p ^ j, fun n => by simp [hp]⟩

theorem eval (p : Polynomial ℕ) : IsPoly fun n => p.eval n := ⟨p, fun _ => rfl⟩

/-- **The Horner step count is polynomial.** Let $cs$ be a list of natural numbers and let
$A : \mathbb{N} \to \mathbb{N}$ be a polynomial function, that is, there is a polynomial $q$ with
natural-number coefficients such that $A(n) = q(n)$ for all $n$. Then $n \mapsto h(n, A(n))$ is a
polynomial function in the same sense, where $h(b, a)$ is the step count of the Horner rounds over
$cs$ with base $b$ from accumulator $a$. -/
theorem hornT (cs : List ℕ) : ∀ {A : ℕ → ℕ}, IsPoly A → IsPoly fun n => Precompute.hornT cs n (A n) := by
  induction cs with
  | nil => intro A _; exact const 0
  | cons a cs ih =>
      intro A hA
      have hstep : IsPoly fun n => hornStep (A n) n := by
        unfold hornStep
        exact ((((((hA.mul ((const 2).mul id |>.add (const 3))).add hA).add (const 2)).add
          (hA.add (const 1))).add ((hA.mul id).add (const 1))).add (const 1))
      exact hstep.add (ih ((hA.mul id).add (const a)))

end IsPoly

theorem fullB_poly {M : FinTM2} (E : Situation.Enc M) (Ys : List (M.Γ M.k₀)) (k : Polynomial ℕ) (c e : ℕ) :
    IsPoly (fullB E Ys k c e) := by
  unfold fullB
  simp only [cB, powB, realB, TOf, mOf, Situation.capH]
  generalize InitFamily.initC _ _ _ = A1
  generalize Family.genC _ _ = A2
  generalize Shift.shC _ _ = A3
  generalize Accept.accC _ _ _ = A4
  generalize Situation.depth M = d
  -- leaves are `n`, constants (generalized above, so no unfolding), `+`, `*`, `^ const`
  repeat' first
    | exact IsPoly.hornT _ (IsPoly.const 0)
    | exact IsPoly.eval _
    | with_reducible exact IsPoly.const _
    | with_reducible exact IsPoly.id
    | with_reducible apply IsPoly.add
    | with_reducible apply IsPoly.mul
    | with_reducible apply IsPoly.pow

/-- **Polynomial time bound of the composed machine.** Let $M$ be a finite multi-stack machine
with encoding data $E$, let $Y$ be a list of symbols of the input stack of $M$, $a$ a symbol of
its output stack, $\iota$ a map from the raw symbols $\mathrm{Fin}\,r$ to symbols of the input
stack, $\sigma$ a symbol of the input stack (the separator), $k$ a polynomial with
natural-number coefficients and $c, e \in \mathbb{N}$. Then there is a polynomial $p$ with
natural-number coefficients such that the following holds for every raw input
$s = s_1 \cdots s_n$ over $\mathrm{Fin}\,r$ and every list $o$ of booleans. Write
$m = n + 1 + k(n)$, $T = (m + c)^e$ and $x = \iota(s_1) \cdots \iota(s_n)\,\sigma$. The full
program on the real generators for $E$, $Y$, $a$, $\iota$, $\sigma$, $k$, $c$ and $e$, started at
its read-loop label with flag false, $s$ on the raw input stack, $o$ on the host output stack and
every other stack empty, reaches the host's final label within $p(n)$ steps, with some flag and
some stack contents in which the host output stack holds the dense encoding of the formula
$\Phi(x, Y, a, m, T)$ emitted by the host, followed by $o$. -/
theorem full_time_poly {r : ℕ} {M : FinTM2} (E : Situation.Enc M) (Ys : List (M.Γ M.k₀))
    (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (s : List (Fin r)) (o : List Bool), ∃ (v : Bool) (S : ∀ k,
        List (FΓ E.layout.g r k)),
      RunLe (fullProg E Ys acc ι sep k c e) (p.eval s.length)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h .fin), v, S⟩ ∧
      S (.h .out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
        (TOf k c e s.length)) ++ o := by
  obtain ⟨p, hp⟩ := fullB_poly E Ys k c e
  refine ⟨p, fun s o => ?_⟩
  obtain ⟨v, S, h1, h2⟩ := full_run E Ys acc ι sep k c e s o
  exact ⟨v, S, h1.mono (hp _).le, h2⟩

end Cslib.Complexity.CookLevin.Precompute
