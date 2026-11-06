/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `D3Init.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/D3Init.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib), and a heartbeat bump for `pre_run`; module docstring rewritten for this
repository (the source's notes and status lines dropped), missing docstrings added, long lines
wrapped.
-/

module

public import MathlibExt.Computability.TuringMachine.StackEmbedding
public import CSLibExt.Computability.Complexity.CookLevin.Situation

/-!
# Cook-Levin: generator machine for the initial-row family

The clauses fixing row `0` of the tableau: the initial label/state, the input `x` followed by a
free certificate block on the input stack (cells after the input are constrained to certificate
symbols or empty), and empty cells everywhere else. `Situation.Enc.initFamily` is the family for a
concrete encoding.

The generator reads the reversed input codes from an extra input stack beside its counter machine
(the stack embedding `liftE` and `run_lift`, an instance of `TM2Embedding.run_embed`), then emits
the clauses with runtime loops over the input, the certificate block and the remaining cells.
`init_gen_capH` gives its run and polynomial step bound.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.InitFamily

open MetaMathlibExt

open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc encodeClause_denseClause denseClause)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out emitS emitOut incS drainS
  xferES copyS mulS mulS_run gapS bud_st stLoop)

/-! ## [PRIM] An input stack beside a counter machine -/

/-- **Stacks of a counter machine with an input stack.** For a counter type $C$, the stacks are
those of the counter machine with counters $C$ (its output stack and one counter stack for each
element of $C$), plus one additional input stack. -/
inductive IK (C : Type)
  | b (k : SK C)
  | inp
  deriving DecidableEq, Fintype

/-- **Alphabets of a counter machine with an input stack.** For a counter type $C$ and an input
alphabet $G$, each stack of the counter machine with counters $C$ keeps its alphabet there
(Booleans on the output stack, a single symbol on each counter stack), and the input stack has
alphabet $G$. -/
abbrev IΓ (C G : Type) : IK C → Type
  | .b k => SΓ C k
  | .inp => G

section Lift

variable {C G Λ : Type} [DecidableEq C]

/-- **Stacks of a counter machine with an extra input stack.** Given stack contents $S$ of a
counter machine with counters indexed by $C$ (a list over the alphabet of each of its stacks)
and a list $x$ of symbols from $G$, the combined stack contents give each stack $k$ of the
counter machine the list $S(k)$ and give the extra input stack the list $x$. -/
def emb (S : ∀ k, List (SΓ C k)) (xs : List G) : ∀ k, List (IΓ C G k)
  | .b k => S k
  | .inp => xs

omit [DecidableEq C] in
@[simp] theorem emb_b (S : ∀ k, List (SΓ C k)) (xs : List G) (k : SK C) : emb S xs (.b k) = S k :=
  rfl

omit [DecidableEq C] in
@[simp] theorem emb_inp (S : ∀ k, List (SΓ C k)) (xs : List G) : emb S xs .inp = xs := rfl

theorem update_emb (S : ∀ k, List (SΓ C k)) (xs : List G) (k : SK C) (l : List (SΓ C k)) :
    update (emb S xs) (.b k) l = emb (update S k l) xs := by
  funext k'
  rcases k' with k' | _
  · by_cases h : k' = k
    · subst h; simp
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl

theorem update_emb_inp (S : ∀ k, List (SΓ C k)) (xs ys : List G) :
    update (emb S xs) .inp ys = emb S ys := by
  funext k'
  rcases k' with k' | _
  · rw [update_of_ne (by simp)]; rfl
  · simp

/-- **The counter stacks inside the generator's stacks.** For a counter index type $C$ and an
input alphabet $G$, the stack embedding of a counter machine over $C$ into the same machine with
one extra input stack over $G$: each stack (the output stack or a counter) goes to its copy among
the extended machine's stacks, with the identity map on its alphabet. -/
def liftE : SEmb (SΓ C) (IΓ C G) where
  e := IK.b
  inj := fun _ _ h => by cases h; rfl
  ι := fun _ => Equiv.refl _

omit [DecidableEq C] in
theorem agree_emb (S : ∀ k, List (SΓ C k)) (xs : List G) : Agree liftE S (emb S xs) := by
  intro k; exact (List.map_id _).symm

/-- **Run lifting.** Let $M$ be a counter machine (unit counters indexed by $C$ and a Boolean
output stack) and $M'$ a machine on the same stacks plus an input stack over $G$, such that $M'$
embeds $M$ along the inclusion of the counter stacks with the same labels (at every label whose
statement is not the halt statement, $M'$ runs $M$'s statement). If $M$ runs in $n$ steps from
optional label $l$, flag $v$ and stacks $S$ to a label $l'$, flag $v'$ and stacks $S'$, then for
every input list $xs$ over $G$, $M'$ runs in $n$ steps from label $l$, flag $v$, stacks $S$ and
input stack $xs$ to label $l'$, flag $v'$, stacks $S'$ and input stack $xs$.

This is an instance of run embedding. -/
theorem run_lift {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {M' : Λ → TM2.Stmt (IΓ C G) Λ Bool}
    (hM : Embeds liftE id M M') (xs : List G) (n : ℕ) (l : Option Λ) (v : Bool)
    (S : ∀ k, List (SΓ C k)) (l' : Λ) (v' : Bool) (S' : ∀ k, List (SΓ C k))
    (h : Run M n ⟨l, v, S⟩ ⟨some l', v', S'⟩) :
    Run M' n ⟨l, v, emb S xs⟩ ⟨some l', v', emb S' xs⟩ := by
  obtain ⟨T', r, hA, hF⟩ := run_embed id hM n l v S l' v' S' (emb S xs) h (agree_emb S xs)
  have hT : T' = emb S' xs := by
    funext k
    rcases k with k | _
    · exact (hA k).trans (List.map_id _)
    · exact hF .inp (fun k h => by cases h)
  rw [Option.map_id] at r
  exact hT ▸ r

theorem runLe_lift {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {M' : Λ → TM2.Stmt (IΓ C G) Λ Bool}
    (hM : Embeds liftE id M M') (xs : List G) {B : ℕ} {l : Option Λ} {v : Bool}
    {S : ∀ k, List (SΓ C k)} {l' : Λ} {v' : Bool} {S' : ∀ k, List (SΓ C k)}
    (h : RunLe M B ⟨l, v, S⟩ ⟨some l', v', S'⟩) :
    RunLe M' B ⟨l, v, emb S xs⟩ ⟨some l', v', emb S' xs⟩ :=
  let ⟨n, hn, r⟩ := h; ⟨n, hn, run_lift hM xs n l v S l' v' S' r⟩

end Lift

/-! ## [PRIM] Reading one input symbol into the label -/

section Read

variable {C Λ : Type} [DecidableEq C] {g : ℕ}

/-- **Read test for one code.** Given labels $\mathrm{hit}(i)$ and $\mathrm{miss}(i)$ for the
codes $i < g$, the read test for code $i$ is the statement, on a counter machine's stacks plus an
input stack of codes, that peeks at the top of the input stack and sets the flag to whether it
equals $i$. If it does, the test pops it and goes to $\mathrm{hit}(i)$; otherwise (including when
the input stack is empty) it goes to $\mathrm{miss}(i)$. -/
def rdS (hit miss : Fin g → Λ) (i : Fin g) : TM2.Stmt (IΓ C (Fin g)) Λ Bool :=
  .peek .inp (fun _ o => decide (o = some i))
    (.branch id (.pop .inp (fun v _ => v) (.goto fun _ => hit i)) (.goto fun _ => miss i))

/-- **The read chain.** Let $M'$ be a machine on a counter machine's stacks plus an input stack of
codes $< g$, with labels $\mathrm{rd}(i)$, $\mathrm{hit}(i)$ and $\mathrm{miss}(i)$ for $i < g$,
such that at $\mathrm{rd}(i)$ it runs the read test for code $i$ with these hit and miss labels,
and $\mathrm{miss}(i) = \mathrm{rd}(i + 1)$ whenever $i + 1 < g$. Then for all counter stacks $S$,
codes $c$, input lists $xs$, all $k$ and codes $i$ with $i + k = c$, and every flag $v$, the
machine $M'$ goes in exactly $k + 1$ steps from label $\mathrm{rd}(i)$, flag $v$, stacks $S$ and
input $c$ followed by $xs$ to label $\mathrm{hit}(c)$, flag true, stacks $S$ and input $xs$. -/
theorem read_run {M' : Λ → TM2.Stmt (IΓ C (Fin g)) Λ Bool} {rd hit miss : Fin g → Λ}
    (hrd : ∀ i, M' (rd i) = rdS hit miss i)
    (hmiss : ∀ i : Fin g, ∀ h : i.val + 1 < g, miss i = rd ⟨i.val + 1, h⟩)
    (S : ∀ k, List (SΓ C k)) (c : Fin g) (xs : List (Fin g)) :
    ∀ k (i : Fin g), i.val + k = c.val → ∀ v : Bool,
      Run M' (k + 1) ⟨some (rd i), v, emb S (c :: xs)⟩ ⟨some (hit c), true, emb S xs⟩ := by
  intro k
  induction k with
  | zero =>
      intro i hi v
      obtain rfl : i = c := Fin.ext (by omega)
      refine Run.single ?_
      simp [hrd, rdS, TM2.stepAux, update_emb_inp]
  | succ k ih =>
      intro i hi v
      have hne : c ≠ i := fun h => by subst h; omega
      have hlt : i.val + 1 < g := by have := c.2; omega
      refine Run.head (d := ⟨some (rd ⟨i.val + 1, hlt⟩), false, emb S (c :: xs)⟩) ?_
        (ih ⟨i.val + 1, hlt⟩ (by simp only; omega) false)
      simp [TM2.step, hrd, rdS, TM2.stepAux, hne, hmiss i hlt]

end Read

/-! ## [FAM] The family (pure specification) -/

section Spec

variable (L : Layout) (ic k0 : ℕ) (ycs : List ℕ)

/-- **Empty-cell variable of the initial row.** For a variable layout $L$, a stack number $k_0$, a
number $H$ of tracked depths per stack and a depth $j$, this is the index of the cell variable
of $L$ at time $0$ for stack $k_0$, depth $j$ and symbol code $0$ (the empty cell $\bot$), namely
$A + (k_0 H + j)\,g$, where $A$ is the size of the label/state block of $L$ and $g$ is its number
of symbol codes. -/
def zB (H j : ℕ) : ℕ := L.cIdx H 0 k0 j 0

/-- **Start-code clause of the initial row (I1).** For a layout $L$, a label/state code $i_c$ and
natural numbers $T$ and $H$, the start-code formula consists of a single clause: the dense clause
over the variables of $L$ for $T$ time steps and depth $H$ whose only literal is the positive
literal on the time-$0$ label/state variable with code $i_c$. -/
def iCode (T H : ℕ) : CNF := [denseClause (L.numVars T H) [(L.xIdx H 0 ic, true)]]

/-- **Row-0 clauses for the other stacks.** Let $L$ be a layout with label block size $A$, $K$
stacks and $g$ symbol codes, let $k_0$ be a stack, and let $T, H$ be natural numbers. This is the
CNF over $V = (T + 1)(A + KHg)$ variables that has, for every stack $k < K$ with $k \ne k_0$ and
every depth $j < H$ (stacks in increasing order, then depths in increasing order), the dense
clause over $V$ variables whose only literal is the positive literal of variable
$A + (kH + j)g$, the row-$0$ variable saying that stack $k$ holds code $0$ (the empty cell) at
depth $j$. -/
def iOther (T H : ℕ) : CNF :=
  ((List.range L.KK).filter (· ≠ k0)).flatMap fun k =>
    (List.range H).map fun j => denseClause (L.numVars T H) [(L.cIdx H 0 k j 0, true)]

/-- **Input clauses of the initial row (I3).** For a layout $L$ with $g$ symbol codes, a stack
number $k_0$, a list $x = (x_0, \dots, x_{\ell - 1})$ of codes below $g$ and natural numbers $T$
and $H$, the input formula has, for each $j = 0, 1, \dots, \ell - 1$ in order, one dense clause
over the variables of $L$ for $T$ time steps and depth $H$, whose only literal is the positive
literal on the time-$0$ cell variable of stack $k_0$ at depth $j$ with code $x_j$. -/
def iIn (xs : List (Fin L.g)) (T H : ℕ) : CNF :=
  (List.range xs.length).map fun j => denseClause (L.numVars T H)
    [(L.cIdx H 0 k0 j ((xs[j]?).elim 0 Fin.val), true)]

/-- **Certificate clauses of the initial row (I4).** Let $L$ be a layout with label block size
$A$, $K$ stacks and $g$ symbol codes, let $k_0$ be a stack, let $y = (y_1, \dots, y_r)$ be a list
of natural numbers and let $n, m, T, H$ be natural numbers. For a depth $j$ and a code $x$ write
$C_{j,x} = A + (k_0 H + j)g + x$ for the row-$0$ variable saying that stack $k_0$ holds code $x$
at depth $j$. This is the CNF over $V = (T + 1)(A + KHg)$ variables that has, for
$i = 0, 1, \dots, m - n - 1$ in order (no clauses if $m \le n$), the dense clause over $V$
variables whose literals are the positive literals of the variables $C_{n+i,0}$, $C_{n+i,y_1}$,
$\dots$, $C_{n+i,y_r}$: the cell at depth $n + i$ is empty or holds one of the codes in $y$.

In use, $y$ lists the certificate codes, sorted and distinct. -/
def iCert (n m T H : ℕ) : CNF :=
  (List.range (m - n)).map fun i => denseClause (L.numVars T H)
    ((zB L k0 H (n + i), true) :: ycs.map fun c => (L.cIdx H 0 k0 (n + i) c, true))

/-- **Row-0 prefix clauses.** Let $L$ be a layout with label block size $A$, $K$ stacks and $g$
symbol codes, let $k_0$ be a stack, let $n, m, T, H$ be natural numbers, and write
$z_j = A + (k_0 H + j)g$ for the row-$0$ variable saying that stack $k_0$ holds code $0$ (the
empty cell) at depth $j$. This is the CNF over $V = (T + 1)(A + KHg)$ variables that has, for
$i = 0, 1, \dots, m - n - 1$ in order (no clauses if $m \le n$), the dense clause over $V$
variables whose literals are the negative literal of variable $z_{n+i}$ and the positive literal
of variable $z_{n+i+1}$: an empty cell at depth $n + i$ forces an empty cell at depth
$n + i + 1$. -/
def iPre (n m T H : ℕ) : CNF :=
  (List.range (m - n)).map fun i => denseClause (L.numVars T H)
    [(zB L k0 H (n + i), false), (zB L k0 H (n + i + 1), true)]

/-- **Row-0 tail clauses.** Let $L$ be a layout with label block size $A$, $K$ stacks and $g$
symbol codes, let $k_0$ be a stack, let $m, T, H$ be natural numbers, and write
$z_j = A + (k_0 H + j)g$ for the row-$0$ variable saying that stack $k_0$ holds code $0$ (the
empty cell) at depth $j$. This is the CNF over $V = (T + 1)(A + KHg)$ variables that has, for
$i = 0, 1, \dots, H - m - 1$ in order (no clauses if $H \le m$), the dense clause over $V$
variables whose only literal is the positive literal of variable $z_{m+i}$. -/
def iTail (m T H : ℕ) : CNF :=
  (List.range (H - m)).map fun i => denseClause (L.numVars T H) [(zB L k0 H (m + i), true)]

/-- **The init family.** Let $L$ be a layout, let $i_c$ be a label/state code, let $k_0$ be a
stack, let $y$ be a list of natural numbers, let $x$ be a list of symbol codes of $L$ of length
$\ell$, and let $m, T, H$ be natural numbers. The init family is the CNF formula obtained by
concatenating, in this order: the start-code clause of the initial row for $i_c$, $T$, $H$ (I1);
the row-$0$ clauses for the stacks other than $k_0$ for $T$, $H$ (I2); the input clauses of the
initial row for $k_0$, $x$, $T$, $H$ (I3); the certificate clauses of the initial row for $k_0$,
$y$, $n = \ell$, $m$, $T$, $H$ (I4); the row-$0$ prefix clauses for $k_0$, $n = \ell$, $m$, $T$,
$H$ (I5); and the row-$0$ tail clauses for $k_0$, $m$, $T$, $H$ (I6). -/
def initFam (xs : List (Fin L.g)) (m T H : ℕ) : CNF :=
  iCode L ic T H ++ iOther L k0 T H ++ iIn L k0 xs T H ++ iCert L k0 ycs xs.length m T H ++
    iPre L k0 xs.length m T H ++ iTail L k0 m T H

end Spec

/-! ## [FAM] The generator machine -/

/-- **Counters of the initial-row generator.** The unit-counter stacks of the generator are
indexed by a finite type with 27 distinct elements: Tn, Xn, En, Fn, Gc, Mm, Hs, HG, Wc, Vc, KA,
ZA, Z45, Z6, Z1, Z2, N1, N2, CB, Zr, P, Q, tmp, md, c1, c2 and Id. Equality on it is
decidable. -/
inductive CK
  | Tn | Xn | En | Fn | Gc | Mm | Hs | HG | Wc | Vc | KA | ZA | Z45 | Z6 | Z1 | Z2 | N1 | N2
  | CB | Zr | P | Q | tmp | md | c1 | c2 | Id
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Xn, CK.En, CK.Fn, CK.Gc, CK.Mm, CK.Hs, CK.HG, CK.Wc, CK.Vc, CK.KA, CK.ZA,
      CK.Z45, CK.Z6, CK.Z1, CK.Z2, CK.N1, CK.N2, CK.CB, CK.Zr, CK.P, CK.Q, CK.tmp, CK.md, CK.c1, CK.c2, CK.Id], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Loop phases of the initial-row generator.** The five phase loops of the generator for the
initial-row clauses, in the order the generator runs them (its input loop runs between the
certificate phase and the two stack phases): the tail phase (the row-$0$ cells of the stack $k_0$
holding the input, past the certificate block, are empty), the prefix phase (an empty cell in the
certificate block is followed by an empty cell), the certificate phase (each certificate cell is
empty or holds a certificate code), and two stack phases making every stack other than $k_0$
empty, first the stacks $k > k_0$, then the stacks $k < k_0$. -/
inductive PH
  | tail | pre | cert | o2 | o1
  deriving DecidableEq
instance PH.instFintypeEnumFix : Fintype PH where
  elems := ⟨↑[PH.tail, PH.pre, PH.cert, PH.o2, PH.o1], by decide⟩
  complete := fun x => by cases x <;> decide

namespace PH

/-- **Loop-count counter of a phase (initial-row generator).** Let $k_0$ be the index of the
input stack in the tableau layout. For a loop phase $p$, the generator counter whose units count
the remaining iterations of the loop of $p$: Fn for the I6 phase, En for both the I5 and the I4
phase, N2 for the I2 phase over the stacks $k > k_0$, and N1 for the I2 phase over the stacks
$k < k_0$. -/
def cN : PH → CK
  | tail => .Fn
  | pre => .En
  | cert => .En
  | o2 => .N2
  | o1 => .N1

/-- **Base counter of a phase (initial-row generator).** Let $k_0$ be the index of the input
stack in the tableau layout. For a loop phase $p$, the generator counter holding the base of the
loop of $p$, the cell base of its iteration $0$: Z6 for the I6 phase, Z45 for both the I5 and the
I4 phase, Z2 for the I2 phase over the stacks $k > k_0$, and Z1 for the I2 phase over the stacks
$k < k_0$. -/
def cZ : PH → CK
  | tail => .Z6
  | pre => .Z45
  | cert => .Z45
  | o2 => .Z2
  | o1 => .Z1

end PH

/-- **Clause kinds of the initial-row generator.** For $g, n \in \mathbb{N}$, a clause kind is
either the start-code clause (I1), an input clause (I3) with a symbol code $c < g$, or the clause
of one of the five loop phases $p$. The parameter $n$ only indexes the type. There are finitely
many clause kinds and their equality is decidable. -/
inductive CL (g n : ℕ)
  | code
  | inp (c : Fin g)
  | ph (p : PH)
  deriving DecidableEq, Fintype

-- `n` only indexes the type (the literal routine's instances differ by `n`); the derived
-- `Fintype` instance's proxy type does not use it.
attribute [nolint unusedArguments] CL.proxyType

namespace CL

variable {g n : ℕ}

/-- **Number of literals of a clause kind.** For clause kinds over $g$ codes and $n$ certificate
codes, a clause of the certificate phase has $n + 1$ literals, a clause of the prefix phase has $2$,
and every other clause kind has $1$. -/
def nl : CL g n → ℕ
  | ph .cert => n + 1
  | ph .pre => 2
  | _ => 1

/-- **Literal offsets.** Fix numbers $i_c$ and $g'$ and a list $y = (y_1, \dots, y_r)$ of
numbers. The offset from the clause base of literal $l$ in a clause of kind $c$ is $i_c$ for the
start-code clause; $x$ for the input clause with code $x$; for the certificate phase, $y_l$ if
$1 \le l \le r$ and $0$ otherwise; for the prefix phase, $0$ if $l = 0$ and $g'$ otherwise; and $0$
for the other three phases. -/
def off (ic g' : ℕ) (ycs : List ℕ) : CL g n → ℕ → ℕ
  | code, _ => ic
  | inp c, _ => c
  | ph .cert, l => (0 :: ycs).getD l 0
  | ph .pre, l => if l = 0 then 0 else g'
  | ph _, _ => 0

/-- **Literal signs of an init-family clause kind.** For a clause kind $c$ of the init-family
generator and a literal index $l \in \mathbb{N}$, the sign of literal $l$ of $c$ is positive in
every case except one: for the prefix-form phase (clause group I5), literal $0$ is negative and
every literal $l \ne 0$ is positive. -/
def sg : CL g n → ℕ → Bool
  | ph .pre, l => decide (l ≠ 0)
  | _, _ => true

/-- **Base counter of a clause kind (initial-row generator).** For a clause kind $c$, the
generator counter whose value is added to the literal offsets of $c$ to give the literal
positions: the counter Zr for the start-code clause (I1), and the counter CB for every other
clause kind. -/
def bc : CL g n → CK
  | code => .Zr
  | _ => .CB

theorem bc_ne (c : CL g n) : c.bc ≠ .Q ∧ c.bc ≠ .tmp ∧ c.bc ≠ .P := by
  cases c <;> simp [bc]

theorem nl_le (c : CL g n) : c.nl ≤ n + 2 := by
  rcases c with _ | _ | p
  · simp [nl]
  · simp [nl]
  · cases p <;> simp [nl]

end CL

/-- **Labels of the first precomputation part.** The finite type of labels with which the
generator sets the counters $G_c = g$, $M_m = m$, $H_s = H$, $HG = H \cdot g$, $W_c = W$ and
$V_c = V$, where $g$ is the number of symbol codes, $m$ the end of the certificate block, $H$ the
stack height, $W$ the row width and $V$ the number of variables. It consists of thirteen single
labels and three multiplication loops, each with one label per multiplication stage. -/
inductive PS1
  | eg | cpM1 | cpM2 | cpE1 | cpE2 | cpH1 | cpH2 | cpF1 | cpF2 | hg (s : MS)
  | wA | wK | w (s : MS) | wD | inc | v (s : MS)
  deriving DecidableEq, Fintype

/-- **Labels of the second precomputation part.** The finite type of labels with which the
generator computes the row-0 cell bases $Z_A, Z_{45}, Z_6, Z_1, Z_2$ and the loop counts
$N_1, N_2$. It consists of sixteen single labels and five multiplication loops, each with one label
per multiplication stage. -/
inductive PS2
  | zA | zK | z (s : MS) | zD | f1 | f2 | f (s : MS) | s1 | s2 | s (s : MS) | z1
  | t1 | t2 | t3 | t4 | nK | n (s : MS) | nD | qK | q (s : MS) | qD
  deriving DecidableEq, Fintype

/-- **Stages of the literal routine (initial-row generator).** The stages of the generator's
routine that emits one literal of a clause: two stages copying the clause base into a target
counter, a stage adding the literal's offset to the target, a stage decrementing the position
counter, a stage comparing the position with the target, two restore stages for each comparison
outcome (less, equal or greater), a stage emitting one empty slot, a halting error stage, a stage
emitting the literal's slot, and a stage draining the target counter. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- **Labels of the initial-row generator.** For natural numbers $g$ and $n$, the labels are: a
label for each stage of the first precomputation part and one for each stage of the second; for
each loop phase $p$, a loop-head label, a counter-reset label, two base-copy labels, a
multiplication label for each multiplication stage and a base-drain label; for the input loop,
a head label, two base-copy labels, a multiplication label for each multiplication stage, a read
test for each code $i < g$ and a base-drain label; an error label; for each clause kind $c$ for
$g$ and $n$, a clause-start label, two labels copying the variable count, a literal label for
each literal index $l < n + 2$ and each literal stage, and a label emitting the leading gap; and
a final label. The label type has decidable equality and is finite. -/
inductive GL (g n : ℕ)
  | pre1 (s : PS1) | pre2 (s : PS2)
  | hd (p : PH) | rs (p : PH) | b1 (p : PH) | b2 (p : PH) | bM (p : PH) (s : MS) | dr (p : PH)
  | i3h | i3b1 | i3b2 | i3M (s : MS) | rd (i : Fin g) | i3d | bad
  | e00 (c : CL g n) | cv1 (c : CL g n) | cv2 (c : CL g n)
  | lit (c : CL g n) (l : Fin (n + 2)) (s : LS) | fin (c : CL g n)
  | done
  deriving DecidableEq, Fintype

namespace GL

variable {g n : ℕ}

/-- **Entry label of a literal routine (initial-row generator).** For a clause kind $c$ and
$l \in \mathbb{N}$, among the generator labels with parameters $g$ and $n$: the first stage of the
routine for literal $l$ of $c$ if $l < n + 2$, and the label $\mathrm{done}$ otherwise (that
case is never used). -/
def litL (c : CL g n) (l : ℕ) : GL g n := if h : l < n + 2 then .lit c ⟨l, h⟩ .cp1 else .done

/-- **Label after a literal routine (initial-row generator).** Let $g, n \in \mathbb{N}$, let $c$
be a clause kind of the generator with parameters $g$ and $n$, and let $l \in \mathbb{N}$. If
$l = 0$, the label is the final routine of $c$, which emits the leading gap. If $l \ge 1$, it is
the start of the routine for literal $l - 1$ of $c$ when $l - 1 < n + 2$, and the halting label
otherwise. The generator goes here after the routine for literal $l$, and with $l$ the number
of literals of $c$ before its first literal routine, so literals are emitted from the last to
the first. -/
def after (c : CL g n) (l : ℕ) : GL g n := if l = 0 then .fin c else litL c (l - 1)

/-- **Label after a phase loop.** Write $k_0$ for the stack holding the input. The label the
generator moves to when the loop of phase $p$ finishes: the loop head of the prefix phase after
the tail phase, the loop head of the certificate phase after the prefix phase, the head of the
input loop after the certificate phase, the loop head of the phase for the stacks $k < k_0$ after
the phase for the stacks $k > k_0$, and the first step of the start-code clause after the phase
for the stacks $k < k_0$. -/
def next : PH → GL g n
  | .tail => .hd .pre
  | .pre => .hd .cert
  | .cert => .i3h
  | .o2 => .hd .o1
  | .o1 => .e00 .code

/-- **Label after a clause.** The label the generator moves to after emitting a clause of kind $c$:
the halting label after the start-code clause, the end of the input-loop iteration (which drains
the clause base) after an input clause, and the end of the loop iteration of phase $p$ (which
drains the clause base) after a clause of phase $p$. -/
def nextC : CL g n → GL g n
  | .code => .done
  | .inp _ => .i3d
  | .ph p => .dr p

/-- **The first read test.** For $g, n \in \mathbb{N}$, the generator label that tests for input
code $0$ when $g > 0$, and the error label when $g = 0$. -/
def rd0 : GL g n := if h : 0 < g then .rd ⟨0, h⟩ else .bad

/-- **Label after a failed read test.** For a code $i < g$, the label reached when the read test
for $i$ fails is the read test for $i + 1$ if $i + 1 < g$, and the halting error label otherwise. -/
def miss (i : Fin g) : GL g n := if h : i.val + 1 < g then .rd ⟨i.val + 1, h⟩ else .bad

theorem litL_of_lt {c : CL g n} {l : ℕ} (h : l < n + 2) : (litL c l : GL g n) = .lit c ⟨l,
    h⟩ .cp1 :=
  dite_eq_left h

end GL

section Machine

variable (L : Layout) (ic k0 : ℕ) (ycs : List ℕ)

/-- **Labels of the initial-row generator for a layout.** For a layout $L$ and a list $y$ of
certificate codes, the label type of the generator is the type of labels of the initial-row
generator with parameters $g$, the number of symbol codes of $L$, and $n$, the length of $y$. -/
abbrev Lb := GL L.g ycs.length

/-- **The literal routine of the initial-row generator.** For a clause kind $c$ and a literal
index $l < n + 2$, where $n$ is the number of certificate codes, the counter program at the
stages of the routine for literal $l$ of $c$. It copies the base counter of $c$ into the counter
$Q$ (restoring the base counter through a scratch counter) and adds the offset of literal $l$ to
$Q$. It then repeats: pop a unit from the counter $P$ (halting if $P$ is empty) and compare $P$
with $Q$, restoring both. If they are equal, it prepends the slot code of the sign of literal $l$
to the output, empties $Q$ and goes to the label before literal $l$: the routine for literal
$l - 1$, or the leading gap of the clause if $l = 0$. Otherwise it prepends the gap code $01$ to
the output and repeats. -/
def litP (c : CL L.g ycs.length) (l : Fin (ycs.length + 2)) : LS → TM2.Stmt (SΓ CK) (Lb L ycs) Bool
  | .cp1 => xfer (.c c.bc) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c l .cp1) (.lit c l .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c c.bc, ()⟩] (.lit c l .cp2) (.lit c l .eo)
  | .eo => emitR (.c .Q) (List.replicate (c.off ic L.g ycs l) ()) (.lit c l .dec)
  | .dec => decr (.c .P) (.lit c l .bad) (.lit c l .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c l .cmp)
      (.lit c l (.r .lt)) (.lit c l (.r .eq)) (.lit c l (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c l (.r o)) (.lit c l (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c l (.rB o))
      (if o = .eq then .lit c l .slot else .lit c l .emL)
  | .emL => emitR .out [false, true] (.lit c l .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg l))) (.lit c l .dq)
  | .dq => xfer (.c .Q) [] (.lit c l .dq) (GL.after c l)

/-- **The counter part of the initial-row generator.** Let $L$ be a layout with label block size
$A$, $K$ stacks and $g$ symbol codes, let $i_c$ and $k_0$ be natural numbers and let $y$ be a list
of $n$ certificate codes. The counter part assigns to each label of the initial-row generator for
$g$ and $n$ a statement of the counter machine with the generator's counters and a Boolean flag,
as follows. Every pop sets the flag to whether a unit was popped, and pushes leave it unchanged.
Below, to copy $a$ into $b$ is to use two labels, the first moving $a$ unit by unit into both $b$
and the scratch counter tmp and the second moving tmp back into $a$; to multiply $a \cdot b$ into
$c$ is to run the multiplication routine adding $a \cdot b$ to $c$ with loop index md and scratch
tmp; to add $j$ to $a$ is to prepend $j$ units to $a$ in one step; and to drain $a$ is to empty
it one unit per step.

The first precomputation part adds $g$ to Gc; copies Xn into Mm, En into Mm, Mm into Hs and Fn
into Hs; multiplies Hs $\cdot$ Gc into HG; adds $A$ to Wc and $K$ to KA; multiplies KA $\cdot$ HG
into Wc and drains KA; increments Tn; and multiplies Tn $\cdot$ Wc into Vc. The second part adds
$A$ to ZA and $k_0$ to KA, multiplies KA $\cdot$ HG into ZA and drains KA; copies ZA into Z45 and
multiplies Xn $\cdot$ Gc into Z45; copies ZA into Z6 and multiplies Mm $\cdot$ Gc into Z6; adds
$A$ to Z1; copies ZA into Z2 and HG into Z2; adds $k_0$ to KA, multiplies KA $\cdot$ Hs into N1
and drains KA; adds $K - k_0 - 1$ (truncated subtraction) to KA, multiplies KA $\cdot$ Hs into N2,
drains KA and goes to the loop head of the tail phase.

For a loop phase $p$ with loop-count counter $N_p$ and base counter $Z_p$, the loop head pops
$N_p$; if a unit was popped it pushes a unit onto Id and goes to the body, otherwise it goes to
the counter-reset label, which moves Id back into $N_p$ and goes to the label after the loop of
$p$. The body, made of the base-copy and multiplication labels of $p$, copies $Z_p$ into CB,
multiplies $N_p \cdot$ Gc into CB and goes to the clause-start label of the clause of phase $p$;
the base-drain label of $p$ drains CB and goes to the loop head of $p$. The head of the input
loop pops Xn and goes to the loop head of the phase for the stacks $k > k_0$ if Xn was empty;
otherwise its base-copy and multiplication labels copy ZA into CB, multiply Xn $\cdot$ Gc into CB
and go to the first read test, or to the error label if $g = 0$. The base-drain label of the
input loop drains CB and goes to the head of the input loop. The read tests, the error label and
the final label halt.

For a clause kind $c$, the clause-start label prepends $00$ to the output; the two labels copying
the variable count then copy Vc into $P$ and go to the label after the literal routine for $c$ and
$\mathrm{nl}(c)$, the number of literals of $c$; the labels of literal $l$ of $c$ run the literal
routine of $c$ for $l$; and the leading-gap label of $c$ drains $P$, prepending $01$ to the output
for each unit, and then goes to the label after $c$.

The read tests $\mathrm{rd}(i)$ halt here; the generator replaces them by tests on its input
stack. -/
def prog : Lb L ycs → TM2.Stmt (SΓ CK) (Lb L ycs) Bool
  | .pre1 .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre1 .cpM1)
  | .pre1 .cpM1 => xfer (.c .Xn) [⟨.c .Mm, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpM1) (.pre1 .cpM2)
  | .pre1 .cpM2 => xfer (.c .tmp) [⟨.c .Xn, ()⟩] (.pre1 .cpM2) (.pre1 .cpE1)
  | .pre1 .cpE1 => xfer (.c .En) [⟨.c .Mm, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpE1) (.pre1 .cpE2)
  | .pre1 .cpE2 => xfer (.c .tmp) [⟨.c .En, ()⟩] (.pre1 .cpE2) (.pre1 .cpH1)
  | .pre1 .cpH1 => xfer (.c .Mm) [⟨.c .Hs, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpH1) (.pre1 .cpH2)
  | .pre1 .cpH2 => xfer (.c .tmp) [⟨.c .Mm, ()⟩] (.pre1 .cpH2) (.pre1 .cpF1)
  | .pre1 .cpF1 => xfer (.c .Fn) [⟨.c .Hs, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpF1) (.pre1 .cpF2)
  | .pre1 .cpF2 => xfer (.c .tmp) [⟨.c .Fn, ()⟩] (.pre1 .cpF2) (.pre1 (.hg .head))
  | .pre1 (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre1 (.hg s)) (.pre1 .wA) s
  | .pre1 .wA => emitR (.c .Wc) (List.replicate L.A ()) (.pre1 .wK)
  | .pre1 .wK => emitR (.c .KA) (List.replicate L.KK ()) (.pre1 (.w .head))
  | .pre1 (.w s) => mulS .KA .md .HG .Wc .tmp (fun s => .pre1 (.w s)) (.pre1 .wD) s
  | .pre1 .wD => xfer (.c .KA) [] (.pre1 .wD) (.pre1 .inc)
  | .pre1 .inc => incr (.c .Tn) () (.pre1 (.v .head))
  | .pre1 (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre1 (.v s)) (.pre2 .zA) s
  | .pre2 .zA => emitR (.c .ZA) (List.replicate L.A ()) (.pre2 .zK)
  | .pre2 .zK => emitR (.c .KA) (List.replicate k0 ()) (.pre2 (.z .head))
  | .pre2 (.z s) => mulS .KA .md .HG .ZA .tmp (fun s => .pre2 (.z s)) (.pre2 .zD) s
  | .pre2 .zD => xfer (.c .KA) [] (.pre2 .zD) (.pre2 .f1)
  | .pre2 .f1 => xfer (.c .ZA) [⟨.c .Z45, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .f1) (.pre2 .f2)
  | .pre2 .f2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] (.pre2 .f2) (.pre2 (.f .head))
  | .pre2 (.f s) => mulS .Xn .md .Gc .Z45 .tmp (fun s => .pre2 (.f s)) (.pre2 .s1) s
  | .pre2 .s1 => xfer (.c .ZA) [⟨.c .Z6, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .s1) (.pre2 .s2)
  | .pre2 .s2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] (.pre2 .s2) (.pre2 (.s .head))
  | .pre2 (.s s) => mulS .Mm .md .Gc .Z6 .tmp (fun s => .pre2 (.s s)) (.pre2 .z1) s
  | .pre2 .z1 => emitR (.c .Z1) (List.replicate L.A ()) (.pre2 .t1)
  | .pre2 .t1 => xfer (.c .ZA) [⟨.c .Z2, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .t1) (.pre2 .t2)
  | .pre2 .t2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] (.pre2 .t2) (.pre2 .t3)
  | .pre2 .t3 => xfer (.c .HG) [⟨.c .Z2, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .t3) (.pre2 .t4)
  | .pre2 .t4 => xfer (.c .tmp) [⟨.c .HG, ()⟩] (.pre2 .t4) (.pre2 .nK)
  | .pre2 .nK => emitR (.c .KA) (List.replicate k0 ()) (.pre2 (.n .head))
  | .pre2 (.n s) => mulS .KA .md .Hs .N1 .tmp (fun s => .pre2 (.n s)) (.pre2 .nD) s
  | .pre2 .nD => xfer (.c .KA) [] (.pre2 .nD) (.pre2 .qK)
  | .pre2 .qK => emitR (.c .KA) (List.replicate (L.KK - k0 - 1) ()) (.pre2 (.q .head))
  | .pre2 (.q s) => mulS .KA .md .Hs .N2 .tmp (fun s => .pre2 (.q s)) (.pre2 .qD) s
  | .pre2 .qD => xfer (.c .KA) [] (.pre2 .qD) (.hd .tail)
  | .hd p => forHead (.c p.cN) (.c .Id) () (.b1 p) (.rs p)
  | .rs p => xfer (.c .Id) [⟨.c p.cN, ()⟩] (.rs p) (GL.next p)
  | .b1 p => xfer (.c p.cZ) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.b1 p) (.b2 p)
  | .b2 p => xfer (.c .tmp) [⟨.c p.cZ, ()⟩] (.b2 p) (.bM p .head)
  | .bM p s => mulS p.cN .md .Gc .CB .tmp (.bM p) (.e00 (.ph p)) s
  | .dr p => xfer (.c .CB) [] (.dr p) (.hd p)
  | .i3h => decr (.c .Xn) (.hd .o2) .i3b1
  | .i3b1 => xfer (.c .ZA) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] .i3b1 .i3b2
  | .i3b2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] .i3b2 (.i3M .head)
  | .i3M s => mulS .Xn .md .Gc .CB .tmp .i3M GL.rd0 s
  | .rd _ => .halt
  | .i3d => xfer (.c .CB) [] .i3d .i3h
  | .bad => .halt
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (GL.after c c.nl)
  | .lit c l s => litP L ic ycs c l s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GL.nextC c)
  | .done => .halt

/-- **The initial-row generator.** Let $L$ be a layout with $g$ symbol codes, let $i_c$ and $k_0$
be natural numbers and let $y$ be a list of certificate codes. The generator assigns to each label
of the initial-row generator for $L$ and $y$ a machine statement with a Boolean flag on the stacks
of the counter machine with the generator's counters plus an input stack of codes below $g$, as
follows. At the read test label $\mathrm{rd}(i)$ for a code $i < g$, it is the read test for code
$i$ that goes on success to the clause-start label of the input clause with code $i$ and on
failure to the label after a failed read test for $i$. At every other label, it is the statement
of the counter part of the generator for $L$, $i_c$, $k_0$, $y$ at that label, translated along
the embedding of the counter stacks into the generator's stacks, with labels unchanged. -/
def iprog : Lb L ycs → TM2.Stmt (IΓ CK (Fin L.g)) (Lb L ycs) Bool
  | .rd i => rdS (fun c => .e00 (.inp c)) GL.miss i
  | l => mapS liftE id (prog L ic k0 ycs l)

theorem lifts : Embeds liftE id (prog L ic k0 ycs) (iprog L ic k0 ycs) := by
  intro l
  cases l with
  | rd i => exact Or.inr rfl
  | _ => exact Or.inl rfl

/-- **The init generator as a finite multi-stack machine.** For a layout $L$ with $g$ symbol
codes, a start code $i_c$, a stack $k_0$ and a code list $Y$, this is the finite multi-stack
Turing machine whose stacks are the generator's counters, its Boolean output stack and an extra
input stack, with the extra stack as input stack and the Boolean stack as output stack; whose
stack alphabets are unit symbols on the counters, bits on the output stack and codes below $g$
on the input stack; whose labels are the generator's labels, starting at the first
precomputation label; whose internal state is a Boolean starting at false; and whose transition
function is the generator for $L, i_c, k_0, Y$.

It records only that the generator is a finite machine. -/
def initTM : FinTM2 where
  K := IK CK
  k₀ := .inp
  k₁ := .b .out
  Γ := IΓ CK (Fin L.g)
  Λ := Lb L ycs
  main := .pre1 .eg
  σ := Bool
  initialState := false
  m := iprog L ic k0 ycs

end Machine

/-! ## [FAM] Clause kinds: literal positions -/

section Lits

variable {g n : ℕ} (ic g' : ℕ) (ycs : List ℕ)

/-- **Literals of a clause kind.** Given natural numbers $i_c$ and $g'$, a list $y$ of natural
numbers, a base position $B$ and a clause kind $c$, the literal list of $c$ at base $B$ is the
list of the pairs $(B + \mathrm{off}(c, l), \mathrm{sg}(c, l))$ for $l = 0, 1, \dots,
\mathrm{nl}(c) - 1$ in order, where $\mathrm{nl}(c)$ is the number of literals of $c$,
$\mathrm{off}(c, l)$ is the offset of literal $l$ (computed from $i_c$, $g'$ and $y$) and
$\mathrm{sg}(c, l)$ is its sign. -/
def clits (B : ℕ) (c : CL g n) : List (ℕ × Bool) :=
  (List.range c.nl).map fun l => (B + c.off ic g' ycs l, c.sg l)

/-- **Well-formed init-family clause kinds.** Fix natural numbers $i_c$ and $g'$ and a list $Y$ of
natural numbers, which determine the offsets of the literals of each clause kind from the base.
A clause kind $c$ is well formed when these offsets are strictly increasing: for every
$l \in \mathbb{N}$ with $l + 1$ less than the number of literals of $c$, the offset of literal $l$
of $c$ is less than the offset of literal $l + 1$ of $c$. -/
def WF (c : CL g n) : Prop := ∀ l, l + 1 < c.nl → c.off ic g' ycs l < c.off ic g' ycs (l + 1)

variable {ic g' ycs}

theorem clits_drop (B : ℕ) (c : CL g n) (l : ℕ) :
    (clits ic g' ycs B c).drop l =
      (List.range' l (c.nl - l)).map fun l => (B + c.off ic g' ycs l, c.sg l) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

/-- **Boundary before a literal (initial-row generator).** For a bound $V$, a base $B$, a clause
kind $c$ and $l \in \mathbb{N}$, the boundary before literal $l$ is $B + \mathrm{off}_c(l)$, the
position of literal $l$, when $l$ is less than the number of literals of $c$, and $V$ otherwise.
Here $\mathrm{off}_c(l)$ is the offset of literal $l$ of $c$ determined by the start code $ic$,
the symbol count $g'$ and the certificate codes $ycs$. -/
def bnd (V B : ℕ) (c : CL g n) (l : ℕ) : ℕ := if l < c.nl then B + c.off ic g' ycs l else V

variable (ic g' ycs) in
/-- **Literals of a clause kind in range.** Given the start code $i_c$, a code count $g'$, the
certificate codes $y$, a bound $V$, a base $B$ and a clause kind $c$ of the init generator, all
literals of $c$ are in range when $B + \mathrm{off}_c(l) < V$ for every literal index $l$ less
than the number of literals of $c$, where $\mathrm{off}_c(l)$ is the offset of literal $l$ of $c$
determined by $i_c$, $g'$ and $y$. -/
def InR (V B : ℕ) (c : CL g n) : Prop := ∀ l, l < c.nl → B + c.off ic g' ycs l < V

theorem inc_drop {V B : ℕ} {c : CL g n} (hc : WF ic g' ycs c) (hBV : InR ic g' ycs V B c) (l : ℕ)
    (hl : l ≤ c.nl) : Inc (bnd (ic := ic) (g' := g') (ycs := ycs) V B c l)
      ((clits ic g' ycs B c).drop l) V := by
  rw [clits_drop]
  refine Cslib.Complexity.CookLevin.Family.inc_of_mono _ c.nl V (fun j hj => ?_) (fun j hj => ?_) (c.nl - l) l _
    (by omega) (fun hn => ?_) (fun _ => ?_)
  · simpa using hc j hj
  · exact hBV j (by omega)
  · simp only [bnd]; split_ifs with h
    · omega
    · exact le_rfl
  · simp only [bnd, ite_eq_left (show l < c.nl by omega)]; exact le_rfl

theorem bnd_le {V B : ℕ} {c : CL g n} (hc : WF ic g' ycs c) (hBV : InR ic g' ycs V B c) {l : ℕ}
    (hl : l ≤ c.nl) : bnd (ic := ic) (g' := g') (ycs := ycs) V B c l ≤ V :=
  (inc_drop hc hBV l hl).le

theorem bnd_lt {V B : ℕ} {c : CL g n} (hc : WF ic g' ycs c) (hBV : InR ic g' ycs V B c) {l : ℕ}
    (hl : l < c.nl) : B + c.off ic g' ycs l < bnd (ic := ic) (g' := g') (ycs := ycs) V B c (l + 1) := by
  unfold bnd
  split_ifs with h
  · exact Nat.add_lt_add_left (hc l h) B
  · exact hBV l hl

end Lits

/-! ## [FAM] Correctness: one literal, one clause (in the counter part) -/

section Clause

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

/-- **Empty scratch counters.** An assignment $F$ of natural numbers to the generator's counters
has empty scratch counters when $F(Q) = F(\mathrm{tmp}) = F(\mathrm{md}) = F(c_1) = F(c_2) = 0$.
-/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem Rest.upd {F : CK → ℕ} (h : Rest F) {x : CK} (hQ : x ≠ .Q) (ht : x ≠ .tmp) (hm : x ≠ .md)
    (h1 : x ≠ .c1) (h2 : x ≠ .c2) (n : ℕ) : Rest (update F x n) :=
  ⟨by rw [update_of_ne hQ.symm, h.Q], by rw [update_of_ne ht.symm, h.tmp],
    by rw [update_of_ne hm.symm, h.md], by rw [update_of_ne h1.symm, h.c1],
    by rw [update_of_ne h2.symm, h.c2]⟩

/-- **Run of one literal routine (initial-row generator).** For a layout and a list of $n$
certificate codes, let $c$ be a clause kind with base counter $b$, let $l < n + 2$ be a literal
index with offset $\mathrm{off}(l)$, and let $F$ be counter values whose scratch counters $Q$,
$\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$. Let $\gamma \in \mathbb{N}$, let
$q = F(b) + \mathrm{off}(l)$ and suppose $F(P) = q + \gamma + 1$. Then for every output $o$ and
flag $v$, the counter program runs in at most $\gamma(3q + 6) + 2F(b) + 4q + 9$ steps from the
first stage of the routine for literal $l$ of $c$, with flag $v$, counters $F$ and output $o$, to
the label before literal $l$ (the routine for literal $l - 1$, or the leading gap if $l = 0$),
with flag false, counters $F$ except $P = q$, and output $s \cdot (01)^{\gamma} \cdot o$, where
$s$ is the slot code of the sign of literal $l$. -/
theorem lit_run (c : CL L.g ycs.length) (l : Fin (ycs.length + 2)) (F : CK → ℕ) (hF : Rest F)
    (q gap : ℕ) (hq : q = F c.bc + c.off ic L.g ycs l) (hp : F .P = q + gap + 1) (o : List Bool)
    (v : Bool) :
    RunLe (prog L ic k0 ycs) (gap * (3 * q + 6) + 2 * F c.bc + 4 * q + 9)
      ⟨some (.lit c l .cp1), v, st F o⟩
      ⟨some (GL.after c l), false,
        st (update F .P q) (encodeSlot (some (c.sg l)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  refine Bud.start ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .lit c l .cp1) (l₂ := .lit c l .cp2)
    (next := .lit c l .eo) rfl rfl b1 b2 (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .lit c l .eo) (next := .lit c l .dec) rfl _ _
    _).bud ?_
  refine (gapS (M := prog L ic k0 ycs) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true])
    (dec := .lit c l .dec) (cmpL := .lit c l .cmp) (emitL := .lit c l .emL)
    (ifZero := .lit c l .bad) (next := .lit c l .slot) (r := fun o => .lit c l (.r o))
    (rB := fun o => .lit c l (.rB o))
    (out := fun o => if o = .eq then .lit c l .slot else .lit c l .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L ic k0 ycs) (self := .lit c l .slot) (next := .lit c l .dq) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .lit c l .dq) (next := GL.after c l) (x := .Q)
    rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- **Per-literal step cost of the initial-row generator.** For $V \in \mathbb{N}$, the
per-literal cost is $6V + 9$.

It bounds the steps the generator spends on one literal apart from the gap loop. -/
def litE (V : ℕ) : ℕ := 6 * V + 9

/-- **Step bound for one clause (initial-row generator).** For natural numbers $m$ and $V$,
$$\mathrm{clauseB}(m, V) = V(3V + 6) + m \cdot \mathrm{litE}(V) + 3V + 4,$$
where $\mathrm{litE}(V) = 6V + 9$ is the per-literal cost apart from the gap loop.

It bounds the steps the generator takes to emit one clause with at most $m$ literals over $V$
variables. -/
def clauseB (nm V : ℕ) : ℕ := V * (3 * V + 6) + nm * litE V + 3 * V + 4

/-- **Run of the literal routines of a clause (initial-row generator).** Let $c$ be a clause
kind with $k$ literals at base $B$, the $j$-th at position $B + \mathrm{off}(j)$, such that the
offsets are strictly increasing and every position is below $V$. For $l \le k$ let $b_l$ be
$B + \mathrm{off}(l)$ if $l < k$ and $V$ otherwise, let $\lambda_l$ be the list of literals of
$c$ (position and sign) from index $l$ on, and let the label before literal $l$ be the first
stage of the routine for literal $l - 1$, or the leading-gap stage of $c$ if $l = 0$. Write
$E(a, \lambda)$ for the gap encoding of the slots $a, \dots, V - 1$ with literals $\lambda$. Let
$F$ be counter values whose scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are
$0$ and whose base counter for $c$ equals $B$, and let $o$ be an output. Then for every $l \le k$
and flag $v$ there is a flag $v'$ such that the counter program runs in at most
$b_l(3V + 6) + l(6V + 9)$ steps from the label before literal $l$, with flag $v$, counters $F$
except $P = b_l$ and output $E(b_l, \lambda_l) \cdot 00 \cdot o$, to the leading-gap stage of
$c$, with flag $v'$, counters $F$ except $P = b_0$ and output $E(b_0, \lambda_0) \cdot 00 \cdot o$.
-/
theorem lits_run {V B : ℕ} {c : CL L.g ycs.length} (hc : WF ic L.g ycs c)
    (hBV : InR ic L.g ycs V B c) (F : CK → ℕ) (hF : Rest F) (hB : F c.bc = B) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L ic k0 ycs) (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l * (3 * V + 6) +
          l * litE V)
        ⟨some (GL.after c l), v,
          st (update F .P (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l))
            (gapEnc (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l)
              ((clits ic L.g ycs B c).drop l) V ++ [false, false] ++ o)⟩
        ⟨some (.fin c), v',
          st (update F .P (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0))
            (gapEnc (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0) (clits ic L.g ycs B c) V ++
              [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GL.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hln : l < ycs.length + 2 := lt_of_lt_of_le hlm c.nl_le
      obtain ⟨b1, b2, b3⟩ := c.bc_ne
      set p := B + c.off ic L.g ycs l with hp
      set b := bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c (l + 1) with hb
      have hpb : p < b := bnd_lt hc hBV hlm
      have r := lit_run (ic := ic) (k0 := k0) c ⟨l, hln⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by rw [update_of_ne b3, hB]) (by simp; omega)
        (gapEnc b ((clits ic L.g ycs B c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GL.after, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel, GL.litL_of_lt hln]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits ic L.g ycs B c).drop l =
          (p, c.sg l) :: (clits ic L.g ycs B c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := Cslib.Complexity.CookLevin.Family.gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hc hBV (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hc hBV hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have hBp : B ≤ p := by omega
      rw [update_of_ne b3, hB, Nat.add_one_mul l]
      unfold litE
      omega

/-- **Run of one clause (initial-row generator).** Let $L$ be a layout with $g$ symbol codes, let
$i_c$ and $k_0$ be natural numbers and let $y$ be a list of $n$ certificate codes. Let $c$ be a
clause kind for $g$ and $n$ that is well formed for $i_c$, $g$ and $y$, and let $V, B$ be natural
numbers such that all literals of $c$ at base $B$ (for $i_c$, $g$ and $y$) are in range below $V$.
Let $F$ be counter values of the generator with empty scratch counters such that $F(b) = B$ for
the base counter $b$ of $c$, $F(\mathrm{Vc}) = V$ and $F(P) = 0$. Then for every output $o$ and
flag $v$, the counter part of the generator for $L$, $i_c$, $k_0$, $y$ runs within the step bound
$\mathrm{clauseB}(n + 2, V)$ for one clause from the clause-start label of $c$, with flag $v$,
counters $F$ and output $o$, to the label after $c$, with flag false, counters $F$ and output
$w \cdot o$, where $w$ is the dense encoding of the dense clause over $V$ variables built from the
literal list of $c$ at base $B$ (for $i_c$, $g$ and $y$).
-/
theorem clause_run {V B : ℕ} {c : CL L.g ycs.length} (hc : WF ic L.g ycs c)
    (hBV : InR ic L.g ycs V B c) (F : CK → ℕ) (hF : Rest F) (hB : F c.bc = B) (hV : F .Vc = V)
    (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L ic k0 ycs) (clauseB (ycs.length + 2) V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GL.nextC c), false,
          st F (encodeClause (denseClause V (clits ic L.g ycs B c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L ic k0 ycs) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := GL.after c c.nl)
    rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run (k0 := k0) hc hBV F hF hB o c.nl le_rfl false
  have hbm : bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L ic k0 ycs) (self := .fin c) (next := GL.nextC c) (x := .P) rfl _ _
    _).bud ?_
  have e1 : update (update F .P (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hc hBV 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits ic L.g ycs B c)) =
      rep [false, true] (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0) ++
        gapEnc (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0) (clits ic L.g ycs B c) V ++
          [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      Cslib.Complexity.CookLevin.Family.gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hc hBV (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) c.nl_le
  unfold clauseB
  omega

end Clause

/-! ## [FAM] Correctness: the five phase loops (counter part) -/

namespace PH

theorem cN_ne (p : PH) : p.cN ≠ .Q ∧ p.cN ≠ .tmp ∧ p.cN ≠ .md ∧ p.cN ≠ .c1 ∧ p.cN ≠ .c2 ∧
    p.cN ≠ .CB ∧ p.cN ≠ .P ∧ p.cN ≠ .Vc ∧ p.cN ≠ .Gc ∧ p.cN ≠ .Id ∧ p.cN ≠ p.cZ := by
  cases p <;> decide

theorem cZ_ne (p : PH) : p.cZ ≠ .CB ∧ p.cZ ≠ .tmp ∧ p.cZ ≠ .Id ∧ p.cZ ≠ .md := by
  cases p <;> decide

end PH

section Loops

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

/-- **Step bound for one loop iteration (initial-row generator).** For natural numbers
$m, g, N, V$,

$$\mathrm{bodyB}(m,g,N,V) = 2V + 2 + (N(2g+3) + N + 2) + g + 1 + \mathrm{clauseB}(m,V) + V + 1,$$

where $\mathrm{clauseB}(m, V)$ is the step bound for one clause with at most $m$ literals.

It bounds one iteration of any phase loop, and one I3 iteration including its read. -/
def bodyB (nm g N V : ℕ) : ℕ :=
  2 * V + 2 + (N * (2 * g + 3) + N + 2) + g + 1 + clauseB nm V + V + 1

/-- **One phase-loop iteration of the initial-row generator.** Let $L$ be a layout with $g$
symbol codes, let $ic, k_0 \in \mathbb{N}$, let $ycs$ be a list of $n$ certificate codes, and let
$p$ be a loop phase with base counter $c_Z(p)$ and loop-count counter $c_N(p)$. Let $F$ give the
value of each generator counter, with the scratch counters empty ($\mathrm{Rest}(F)$),
$F(\mathrm{CB}) = F(\mathrm{P}) = 0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(c_Z(p)) = Z$
and $F(c_N(p)) = t$. Suppose $t < N$ and $tg + Z \le V$, the clause kind of $p$ has strictly
increasing literal offsets, and all its literals at base $tg + Z$ lie below $V$. Then for every
output $o$ and flag $v$, the counter program of the generator runs in at most
$\mathrm{bodyB}(n + 2, g, N, V)$ steps from label $b_1(p)$ with flag $v$, counters $F$ and output
$o$ to the loop head of $p$ with flag false, counters $F$ and output
$\mathrm{encodeClause}(\mathrm{denseClause}(V, \mathrm{clits}(tg + Z, p)))$ followed by $o$.
Here $\mathrm{clits}(tg + Z, p)$ are the literals of the clause kind of $p$ at base $tg + Z$. -/
theorem body_run {p : PH} {V Z N t : ℕ} (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hZ : F p.cZ = Z) (ht : F p.cN = t)
    (htN : t < N) (hBV : t * L.g + Z ≤ V) (hW : WF ic L.g ycs (CL.ph p : CL L.g ycs.length))
    (hR : InR ic L.g ycs V (t * L.g + Z) (CL.ph p : CL L.g ycs.length)) (o : List Bool)
    (v : Bool) :
    RunLe (prog L ic k0 ycs) (bodyB (ycs.length + 2) L.g N V) ⟨some (.b1 p), v, st F o⟩
      ⟨some (.hd p), false,
        st F (encodeClause (denseClause V (clits ic L.g ycs (t * L.g + Z)
          (CL.ph p : CL L.g ycs.length))) ++ o)⟩ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := p.cN_ne
  obtain ⟨z1, z2, z3, z4⟩ := p.cZ_ne
  refine Bud.start ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .b1 p) (l₂ := .b2 p) (next := .bM p .head) rfl rfl
    z1 z2 (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := .bM p) (next := .e00 (.ph p)) (a := p.cN)
    (ad := .md) (b := .Gc) (c := .CB) (t := .tmp) (fun _ => rfl) (by cases p <;> decide) _
    (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := update F .CB (t * L.g + Z))
    (by rw [update_idem]; simp [n6, ht, hG, hZ, hCB]) ?_
  have hF' : Rest (update F .CB (t * L.g + Z)) :=
    hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _
  refine (clause_run (k0 := k0) (c := .ph p) hW hR _ hF' (by simp [CL.bc]) (by simp [hV])
    (by simp [hP]) o _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .dr p) (next := .hd p) (x := .CB) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 : t * (2 * L.g + 3) ≤ N * (2 * L.g + 3) := Nat.mul_le_mul_right _ htN.le
    simp only [update_self, update_apply, n6, reduceCtorEq, ite_false, hZ, hCB, ht, hG]
    unfold bodyB
    omega
  · rw [update_idem, update_eq_self_iff.2 hCB.symm]

/-- **One phase loop.** Fix a layout $L$ with $g$ symbol codes, a start code $i_c$, a stack index
$k_0$ and a list $y$ of $n$ certificate codes, and let $M$ be the counter part of the initial-row
generator for these parameters. Let $p$ be a loop phase with loop counter $N_p$ and base counter
$Z_p$, and let $F$ be counter values with the scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$,
$c_1$, $c_2$ empty, $F(\mathrm{CB}) = F(P) = F(\mathrm{Id}) = 0$, $F(\mathrm{Vc}) = V$,
$F(\mathrm{Gc}) = g$, $F(Z_p) = Z$ and $F(N_p) = N$, where $N \le N_b$. Suppose the literal offsets
of phase $p$ (for $i_c$, $g$ and $y$) are strictly increasing and, for every $t < N$,
$tg + Z \le V$ and every literal of the phase-$p$ clause at base $tg + Z$ has position below $V$.
Then for every output $o$ and flag $v$, $M$ goes in at most $N_b(b + 1) + N_b + 2$ steps from the
loop head of phase $p$ with flag $v$, counters $F$ and output $o$ to the label after the loop of
phase $p$ with flag false, counters $F$ and output $B_0 B_1 \cdots B_{N-1}\, o$. Here $B_t$ is the
encoding of the dense clause over $V$ variables with the literals of the phase-$p$ clause at base
$tg + Z$, and $b$ is the loop-iteration cost bound for $n + 2$ literals, $g$ codes, loop count
$N_b$ and $V$ variables. -/
theorem phase_run {p : PH} {V Z N Nb : ℕ} (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hZ : F p.cZ = Z) (hN : F p.cN = N)
    (hId : F .Id = 0) (hNb : N ≤ Nb) (hW : WF ic L.g ycs (CL.ph p : CL L.g ycs.length))
    (hBV : ∀ t < N, t * L.g + Z ≤ V)
    (hR : ∀ t < N, InR ic L.g ycs V (t * L.g + Z) (CL.ph p : CL L.g ycs.length)) (o : List Bool)
    (v : Bool) :
    RunLe (prog L ic k0 ycs) (Nb * (bodyB (ycs.length + 2) L.g Nb V + 1) + Nb + 2)
      ⟨some (.hd p), v, st F o⟩
      ⟨some (GL.next p), false, st F ((List.range N).flatMap
        (fun t => encodeClause (denseClause V (clits ic L.g ycs (t * L.g + Z)
          (CL.ph p : CL L.g ycs.length)))) ++ o)⟩ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := p.cN_ne
  obtain ⟨z1, z2, z3, z4⟩ := p.cZ_ne
  refine (stLoop (M := prog L ic k0 ycs) (c := p.cN) (cd := .Id) (head := .hd p) (body := .b1 p)
    (rest := .rs p) (next := GL.next p) rfl rfl n10 N (bodyB (ycs.length + 2) L.g Nb V) _ F hN hId
    (fun t ht o => ⟨false, ?_⟩) v o).mono ?_
  · have hF' : Rest (update (update F p.cN t) .Id (N - t)) :=
      (hF.upd n1 n2 n3 n4 n5 t).upd (by decide) (by decide) (by decide) (by decide) (by decide) _
    exact body_run (k0 := k0) _ hF' (by simp [n6.symm, hCB])
      (by simp [n7.symm, hP]) (by simp [n8.symm, hV])
      (by simp [n9.symm, hG]) (by simp [n11.symm, z3, hZ])
      (by rw [update_of_ne n10, update_self]) (by omega) (hBV t ht) hW (hR t ht) o true
  · have := Nat.mul_le_mul_right (bodyB (ycs.length + 2) L.g Nb V + 1) hNb
    omega

/-- **Counter part of one I3 iteration.** Let $L$ be a layout with $g$ symbol codes. Suppose the
counters $F$ of the init generator's counter part have $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$,
$c_2$ and $\mathrm{CB}$ equal to $0$, $\mathrm{Gc} = g$, $\mathrm{ZA} = Z$ and
$\mathrm{Xn} = r + 1$. Then for every output $o$ and flag $v$, the counter part, started at the
head of the I3 loop with flag $v$, counters $F$ and output $o$, reaches the first read test (the
halting label if $g = 0$) in at most $1 + (2Z + 2) + (r(2g + 3) + r + 2)$ steps, with flag false,
output $o$, and the counters of $F$ except that $\mathrm{Xn} = r$ and $\mathrm{CB} = rg + Z$. -/
theorem i3pre_run {r ZA : ℕ} (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0) (hG : F .Gc = L.g)
    (hZA : F .ZA = ZA) (hX : F .Xn = r + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L ic k0 ycs) (1 + (2 * ZA + 2) + (r * (2 * L.g + 3) + r + 2))
      ⟨some .i3h, v, st F o⟩
      ⟨some GL.rd0, false, st (update (update F .Xn r) .CB (r * L.g + ZA)) o⟩ := by
  refine Bud.start ?_
  have d := decr_run_cnt (M := prog L ic k0 ycs) (self := .i3h) (ifZero := .hd .o2)
    (ifPos := .i3b1) (k := .c .Xn) (u := ()) rfl v (S := st F o) (n := r) (by simp [hX])
  rw [CounterView.update_st_c] at d
  refine d.bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .i3b1) (l₂ := .i3b2) (next := .i3M .head) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ o).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := .i3M) (next := GL.rd0) (a := .Xn)
    (ad := .md) (b := .Gc) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hZA, hG]
  · congr 2
    rw [update_idem]
    simp [hG, hZA, hCB]

end Loops

/-! ## [FAM] Correctness: the I3 loop (reads the input; in the extended machine) -/

section I3

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

theorem clits_inp {g n : ℕ} (B : ℕ) (c : Fin g) :
    clits ic L.g ycs B (CL.inp c : CL g n) = [(B + c.val, true)] := by
  simp [clits, CL.nl, CL.off, CL.sg]

/-- **The I3 loop.** Let $L$ be a layout with $g$ symbol codes, consider the init generator for a
start code, a stack $k_0$ and a list of $\ell$ certificate codes, and let
$x = (x_0, \dots, x_{s-1})$ be a list of codes $x_j < g$. Suppose its counters $F$ have $Q$,
$\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$, $\mathrm{CB}$ and $P$ equal to $0$,
$\mathrm{Vc} = V$, $\mathrm{Gc} = g$ and $\mathrm{ZA} = Z$, that $jg + Z + g \le V$ for every
$j < s$, and that $s \le N_b$. Then for every $r \le s$, every output $o$ and every flag $v$, the
generator, started at the head of the I3 loop with flag $v$, the counters of $F$ except
$\mathrm{Xn} = r$, output $o$, and $x_{r-1}, \dots, x_1, x_0$ on its input stack (top first),
reaches in at most $r\beta + 1$ steps the head of the I2 loop over the stacks above $k_0$, with
flag false, the counters of $F$ except $\mathrm{Xn} = 0$, an empty input stack, and output
$e_0 e_1 \cdots e_{r-1}$ followed by $o$. Here $e_j$ is the encoding of the dense clause over
$V$ variables whose only literal is the positive literal of variable $jg + Z + x_j$, and
$\beta = 3V^2 + 12V + (\ell + 2)(6V + 9) + (2g + 4)N_b + g + 10$. -/
theorem i3_run {V ZA Nb : ℕ} (xs : List (Fin L.g)) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hZA : F .ZA = ZA)
    (hR : ∀ j < xs.length, j * L.g + ZA + L.g ≤ V) (hNb : xs.length ≤ Nb) :
    ∀ r, r ≤ xs.length → ∀ (o : List Bool) (v : Bool),
      RunLe (iprog L ic k0 ycs) (r * bodyB (ycs.length + 2) L.g Nb V + 1)
        ⟨some .i3h, v, emb (st (update F .Xn r) o) (xs.take r).reverse⟩
        ⟨some (.hd .o2), false, emb (st (update F .Xn 0) ((List.range r).flatMap
          (fun j => encodeClause (denseClause V
            [(j * L.g + ZA + (xs[j]?).elim 0 Fin.val, true)])) ++ o)) []⟩ := by
  intro r
  induction r with
  | zero =>
      intro _ o v
      have d := decr_run_zero (M := prog L ic k0 ycs) (self := .i3h) (ifZero := .hd .o2)
        (ifPos := .i3b1) (k := .c .Xn) rfl v (S := st (update F .Xn 0) o) (by simp)
      have := runLe_lift (lifts L ic k0 ycs) [] (d.le le_rfl)
      simp only [List.take_zero, List.reverse_nil, List.range_zero, List.flatMap_nil,
        List.nil_append, zero_mul, zero_add]
      exact this
  | succ r ih =>
      intro hr o v
      have hrx : r < xs.length := by omega
      set c := xs[r] with hc
      have hg : 0 < L.g := lt_of_le_of_lt (Nat.zero_le _) c.2
      have hB := hR r hrx
      have hcg := c.2
      -- counter part before the read
      have r1 := i3pre_run (L := L) (k0 := k0) (ic := ic) (ycs := ycs) (r := r) (ZA := ZA)
        (update F .Xn (r + 1))
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _)
        (by simp [hCB]) (by simp [hG]) (by simp [hZA]) (by simp) o v
      rw [GL.rd0, dite_eq_left hg, update_idem] at r1
      have htake : (xs.take (r + 1)).reverse = c :: (xs.take r).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hrx]; simp [hc]
      have l1 := runLe_lift (lifts L ic k0 ycs) (c :: (xs.take r).reverse) r1
      rw [htake]
      refine Bud.start (l1.bud ?_)
      -- the read
      have rd := read_run (M' := iprog L ic k0 ycs) (rd := GL.rd)
        (hit := fun c => GL.e00 (CL.inp c)) (miss := GL.miss) (fun _ => rfl)
        (fun i h => dite_eq_left h) (st (update (update F .Xn r) .CB (r * L.g + ZA)) o) c
        (xs.take r).reverse c.val ⟨0, hg⟩ (by simp) false
      refine (rd.bud ?_)
      -- the clause and the drain
      set F2 := update (update F .Xn r) .CB (r * L.g + ZA) with hF2
      have hF2r : Rest F2 :=
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _).upd
          (by decide) (by decide) (by decide) (by decide) (by decide) _
      have cl := clause_run (L := L) (ic := ic) (k0 := k0) (ycs := ycs) (V := V)
        (B := r * L.g + ZA) (c := (CL.inp c : CL L.g ycs.length))
        (fun l hl => by simp [CL.nl] at hl)
        (fun l hl => by simp only [CL.off]; omega) F2 hF2r (by simp [hF2, CL.bc])
        (by simp [hF2, hV]) (by simp [hF2, hP]) o true
      have dr := drainS (M := prog L ic k0 ycs) (self := .i3d) (next := .i3h) (x := .CB) rfl F2
        false (encodeClause (denseClause V (clits ic L.g ycs (r * L.g + ZA) (CL.inp c : CL L.g ycs.length))) ++ o)
      have e2 : update F2 .CB 0 = update F .Xn r := by
        rw [hF2, update_idem]
        exact update_eq_self_iff.2 (by simp [hCB])
      rw [e2] at dr
      have l2 := runLe_lift (lifts L ic k0 ycs) (xs.take r).reverse ((cl.trans (dr.le le_rfl)))
      refine (l2.bud ?_)
      have l3 := ih (Nat.le_of_succ_le hr) (encodeClause (denseClause V
        (clits ic L.g ycs (r * L.g + ZA) (CL.inp c : CL L.g ycs.length))) ++ o) false
      refine (l3.bud (Bud.fin ?_ ?_))
      · simp only [hF2, update_self]
        rw [Nat.add_one_mul r]
        have h1 : r * (2 * L.g + 3) ≤ Nb * (2 * L.g + 3) := Nat.mul_le_mul_right _ (by omega)
        unfold bodyB
        omega
      · rw [clits_inp, List.range_succ, List.flatMap_append, List.flatMap_singleton,
          List.getElem?_eq_getElem hrx]
        simp only [Option.elim_some, List.append_assoc, hc]

end I3

/-! ## [FAM] Literal lists, well-formedness and range of each clause kind -/

section Kinds

variable {g n : ℕ} {ic g' : ℕ} {ycs : List ℕ}

theorem clits_code (B : ℕ) : clits ic g' ycs B (CL.code : CL g n) = [(B + ic, true)] := by
  simp [clits, CL.nl, CL.off, CL.sg]

theorem clits_unit (B : ℕ) {p : PH} (hp : p = .tail ∨ p = .o1 ∨ p = .o2) :
    clits ic g' ycs B (CL.ph p : CL g n) = [(B, true)] := by
  rcases hp with rfl | rfl | rfl <;> simp [clits, CL.nl, CL.off, CL.sg]

theorem clits_pre (B : ℕ) : clits ic g' ycs B (CL.ph .pre : CL g n) = [(B, false), (B + g',
    true)] := by
  simp [clits, CL.nl, CL.off, CL.sg, List.range_succ]

theorem map_range_getD {α : Type} (l : List ℕ) (f : ℕ → α) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem clits_cert (B : ℕ) :
    clits ic g' ycs B (CL.ph .cert : CL g ycs.length) =
      (B, true) :: ycs.map fun c => (B + c, true) := by
  have := map_range_getD (0 :: ycs) (fun c => (B + c, true))
  simp only [List.length_cons, List.map_cons, Nat.add_zero] at this
  simpa [clits, CL.nl, CL.off, CL.sg] using this

theorem wf_unit {c : CL g n} (hc : c.nl = 1) : WF ic g' ycs c := fun l hl => by omega

theorem wf_pre (hg : 0 < g') : WF ic g' ycs (CL.ph .pre : CL g n) := by
  intro l hl
  simp only [CL.nl] at hl
  obtain rfl : l = 0 := by omega
  simpa [CL.off] using hg

theorem wf_cert (hy : (0 :: ycs).Pairwise (· < ·)) : WF ic g' ycs (CL.ph .cert : CL g ycs.length) := by
  intro l hl
  simp only [CL.nl] at hl
  simp only [CL.off]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
  exact List.pairwise_iff_getElem.1 hy l (l + 1) (by simp; omega) (by simp; omega) (by omega)

theorem inr_unit {c : CL g n} (hc : c.nl = 1) {V B : ℕ} (h : B + c.off ic g' ycs 0 < V) :
    InR ic g' ycs V B c := fun l hl => by obtain rfl : l = 0 := by omega
                                          exact h

theorem inr_pre {V B : ℕ} (h : B + g' < V) : InR ic g' ycs V B (CL.ph .pre : CL g n) := by
  intro l hl
  simp only [CL.nl] at hl
  simp only [CL.off]
  split_ifs <;> omega

theorem inr_cert (hyg : ∀ c ∈ ycs, c < g') {V B : ℕ} (h : B + g' ≤ V) (hg : 0 < g') :
    InR ic g' ycs V B (CL.ph .cert : CL g ycs.length) := by
  intro l hl
  simp only [CL.nl] at hl
  simp only [CL.off]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  have : (0 :: ycs)[l]'(by simp; omega) < g' := by
    have hm := List.getElem_mem (show l < (0 :: ycs).length by simp; omega)
    rcases List.mem_cons.1 hm with h0 | h0
    · rw [h0]; exact hg
    · exact hyg _ h0
  omega

end Kinds

/-! ## [FAM] Positions, and the machine's blocks are the family's clauses -/

section Out

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

theorem cIdx0 (H k j x : ℕ) : L.cIdx H 0 k j x = L.A + (k * H + j) * L.g + x := by
  simp [Layout.cIdx]

/-- **Row-0 cells fit in the variable range.** For a layout $L$ with $A$ label/state variables,
$KK$ stacks and $g$ symbol codes, and all $T, H, q \in \mathbb{N}$ with $q < KK \cdot H$, we have
$A + q g + g \le V$, where $V$ is the number of variables of $L$ for time bound $T$ and stack
height $H$. -/
theorem qpos {T H q : ℕ} (hq : q < L.KK * H) : L.A + q * L.g + L.g ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h1 : q * L.g + L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hq
  have h2 : L.A + L.KK * (H * L.g) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

theorem kq_lt {H k j : ℕ} (hk : k < L.KK) (hj : j < H) : k * H + j < L.KK * H := by
  have : k * H + H ≤ L.KK * H := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  omega

theorem enc_code (T H : ℕ) :
    encodeCNF (iCode L ic T H) = encodeClause (denseClause (L.numVars T H)
      (clits ic L.g ycs 0 (CL.code : CL L.g ycs.length))) := by
  simp [encodeCNF, iCode, clits_code, Layout.xIdx]

theorem enc_tail (m T H : ℕ) :
    encodeCNF (iTail L k0 m T H) = (List.range (H - m)).flatMap (fun t => encodeClause
      (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 k0 m 0)
        (CL.ph .tail : CL L.g ycs.length)))) := by
  simp only [encodeCNF, iTail, List.flatMap_map]
  congr 1; funext t
  rw [clits_unit _ (Or.inl rfl), zB, cIdx0, cIdx0]
  congr 4; ring1

theorem enc_pre (n m T H : ℕ) :
    encodeCNF (iPre L k0 n m T H) = (List.range (m - n)).flatMap (fun t => encodeClause
      (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 k0 n 0)
        (CL.ph .pre : CL L.g ycs.length)))) := by
  simp only [encodeCNF, iPre, List.flatMap_map]
  congr 1; funext t
  rw [clits_pre, zB, zB, cIdx0, cIdx0, cIdx0]
  congr 4
  · ring1
  · congr 1; ring1

theorem enc_cert (n m T H : ℕ) :
    encodeCNF (iCert L k0 ycs n m T H) = (List.range (m - n)).flatMap (fun t => encodeClause
      (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 k0 n 0)
        (CL.ph .cert : CL L.g ycs.length)))) := by
  simp only [encodeCNF, iCert, List.flatMap_map]
  congr 1; funext t
  rw [clits_cert, zB, cIdx0, cIdx0]
  have e : t * L.g + (L.A + (k0 * H + n) * L.g + 0) = L.A + (k0 * H + (n + t)) * L.g := by ring1
  rw [e]
  simp [cIdx0]

theorem enc_in (xs : List (Fin L.g)) (T H : ℕ) :
    encodeCNF (iIn L k0 xs T H) = (List.range xs.length).flatMap (fun j => encodeClause
      (denseClause (L.numVars T H) [(j * L.g + L.cIdx H 0 k0 0 0 + (xs[j]?).elim 0 Fin.val,
          true)])) := by
  simp only [encodeCNF, iIn, List.flatMap_map]
  congr 1; funext j
  rw [cIdx0, cIdx0]
  congr 4; ring1

/-- **Concatenating consecutive blocks of indices.** Let $\varphi$ be a function from the natural
numbers to a type $\alpha$ and let $H$, $s$, $r$ be natural numbers. Concatenating, for
$k = s, s + 1, \dots, s + r - 1$ in order, the lists
$[\varphi(kH), \varphi(kH + 1), \dots, \varphi(kH + H - 1)]$ gives the list
$[\varphi(sH), \varphi(sH + 1), \dots, \varphi(sH + rH - 1)]$. -/
theorem flat_blocks {α : Type} (H : ℕ) (φ : ℕ → α) (s : ℕ) : ∀ r : ℕ,
    ((List.range r).map (s + ·)).flatMap (fun k => (List.range H).map fun j => φ (k * H + j)) =
      (List.range (r * H)).map fun q => φ (s * H + q)
  | 0 => by simp
  | r + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flat_blocks H φ s r, Nat.add_one_mul,
      List.range_add, List.map_append, List.map_map]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    congr 1; ring1

theorem filter_ne_range {k0 KK : ℕ} (hk : k0 < KK) :
    (List.range KK).filter (· ≠ k0) = (List.range k0).map (0 + ·) ++
      (List.range (KK - k0 - 1)).map ((k0 + 1) + ·) := by
  conv_lhs => rw [show KK = k0 + 1 + (KK - k0 - 1) by omega, List.range_add, List.range_succ]
  rw [List.filter_append, List.filter_append, List.filter_singleton]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.cond_false, List.append_nil, zero_add,
    List.map_id']
  congr 1
  · exact List.filter_eq_self.2 (fun a ha => by simp at ha; simp; omega)
  · exact List.filter_eq_self.2 (fun a ha => by simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp; omega)

theorem enc_other (hk0 : k0 < L.KK) (T H : ℕ) :
    encodeCNF (iOther L k0 T H) =
      (List.range (k0 * H)).flatMap (fun t => encodeClause (denseClause (L.numVars T H)
        (clits ic L.g ycs (t * L.g + L.A) (CL.ph .o1 : CL L.g ycs.length)))) ++
      (List.range ((L.KK - k0 - 1) * H)).flatMap (fun t => encodeClause
        (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 (k0 + 1) 0 0)
          (CL.ph .o2 : CL L.g ycs.length)))) := by
  have e : iOther L k0 T H = ((List.range L.KK).filter (· ≠ k0)).flatMap fun k =>
      (List.range H).map fun j => (fun q => denseClause (L.numVars T H) [(L.A + q * L.g, true)])
        (k * H + j) := by
    unfold iOther; congr 1; funext k; congr 1; funext j; rw [cIdx0]; simp
  rw [e, filter_ne_range hk0, List.flatMap_append,
    flat_blocks H (fun q => denseClause (L.numVars T H) [(L.A + q * L.g, true)]) 0 k0,
    flat_blocks H (fun q => denseClause (L.numVars T H) [(L.A + q * L.g, true)]) (k0 + 1)]
  simp only [encodeCNF, List.flatMap_append, List.flatMap_map]
  congr 1
  · congr 1; funext t; rw [clits_unit _ (Or.inr (Or.inl rfl))]; congr 4; ring1
  · congr 1; funext t; rw [clits_unit _ (Or.inr (Or.inr rfl)), cIdx0]; congr 4; ring1

end Out

/-! ## [FAM] Precomputation and the whole generator -/

section Top

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

/-- **Initial counters of the init generator.** For natural numbers $T, n, e, f$, the counters
$\mathrm{Tn}$, $\mathrm{Xn}$, $\mathrm{En}$ and $\mathrm{Fn}$ of the generator hold $T$, $n$, $e$
and $f$ respectively, and every other counter holds $0$.

In use, $n$ is the length of the input code list, $e = m - n$ and $f = H - m$, where $m$ is the
depth at which the certificate block ends and $H$ is the stack height. -/
def initF (T n e f : ℕ) : CK → ℕ
  | .Tn => T
  | .Xn => n
  | .En => e
  | .Fn => f
  | _ => 0

/-- **Counters after the precomputation.** For a layout $L$ with $A$ label/state variables, $K$
stacks and $g$ symbol codes, a stack index $k_0$ and numbers $T, n, e, f$, write $H = n + e + f$.
The counter values after the precomputation are $\mathrm{Tn} = T + 1$, $\mathrm{Xn} = n$,
$\mathrm{En} = e$, $\mathrm{Fn} = f$, $\mathrm{Gc} = g$, $\mathrm{Mm} = n + e$, $\mathrm{Hs} = H$,
$\mathrm{HG} = Hg$, $\mathrm{Wc} = A + KHg$ (the row width), $\mathrm{Vc} = (T + 1)(A + KHg)$ (the
number of variables), $\mathrm{ZA} = A + k_0Hg$, $\mathrm{Z45} = A + (k_0H + n)g$,
$\mathrm{Z6} = A + (k_0H + n + e)g$, $\mathrm{Z1} = A$, $\mathrm{Z2} = A + (k_0 + 1)Hg$,
$\mathrm{N1} = k_0H$ and $\mathrm{N2} = (K - k_0 - 1)H$ (truncated subtraction), and $0$ for every
other counter. -/
def preF (L : Layout) (k0 T n e f : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Xn => n
  | .En => e
  | .Fn => f
  | .Gc => L.g
  | .Mm => n + e
  | .Hs => n + e + f
  | .HG => (n + e + f) * L.g
  | .Wc => L.rowW (n + e + f)
  | .Vc => L.numVars T (n + e + f)
  | .ZA => L.cIdx (n + e + f) 0 k0 0 0
  | .Z45 => L.cIdx (n + e + f) 0 k0 n 0
  | .Z6 => L.cIdx (n + e + f) 0 k0 (n + e) 0
  | .Z1 => L.A
  | .Z2 => L.cIdx (n + e + f) 0 (k0 + 1) 0 0
  | .N1 => k0 * (n + e + f)
  | .N2 => (L.KK - k0 - 1) * (n + e + f)
  | _ => 0

/-- **Step bound for the precomputation.** For a layout $L$ with $A$ label/state variables, $K$
stacks and $g$ symbol codes, and numbers $k_0, q, T, n, e, f$, write $h = n + e + f$. The bound is

$$
1 + (2n + 2) + (2e + 2) + (2(n + e) + 2) + (2f + 2) + (h(2g + 3) + h + 2) + 1 + 1 +
(K(2hg + 3) + K + 2) + (K + 1) + 1 + ((T + 1)(2(Khg + A) + 3) + (T + 1) + 2) + 1 + 1 +
(k_0(2hg + 3) + k_0 + 2) + (k_0 + 1) + (2(k_0 hg + A) + 2) + (n(2g + 3) + n + 2) +
(2(k_0 hg + A) + 2) + ((n + e)(2g + 3) + (n + e) + 2) + 1 + (2(k_0 hg + A) + 2) + (2hg + 2) +
1 + (k_0(2h + 3) + k_0 + 2) + (k_0 + 1) + 1 + (q(2h + 3) + q + 2) + (q + 1).
$$

The precomputation uses it with $q = K - k_0 - 1$. -/
def preB (L : Layout) (k0 q T n e f : ℕ) : ℕ :=
  1 + (2 * n + 2) + (2 * e + 2) + (2 * (n + e) + 2) + (2 * f + 2) +
    ((n + e + f) * (2 * L.g + 3) + (n + e + f) + 2) + 1 + 1 +
    (L.KK * (2 * ((n + e + f) * L.g) + 3) + L.KK + 2) + (L.KK + 1) + 1 +
    ((T + 1) * (2 * (L.KK * ((n + e + f) * L.g) + L.A) + 3) + (T + 1) + 2) + 1 + 1 +
    (k0 * (2 * ((n + e + f) * L.g) + 3) + k0 + 2) + (k0 + 1) +
    (2 * (k0 * ((n + e + f) * L.g) + L.A) + 2) + (n * (2 * L.g + 3) + n + 2) +
    (2 * (k0 * ((n + e + f) * L.g) + L.A) + 2) + ((n + e) * (2 * L.g + 3) + (n + e) + 2) + 1 +
    (2 * (k0 * ((n + e + f) * L.g) + L.A) + 2) + (2 * ((n + e + f) * L.g) + 2) + 1 +
    (k0 * (2 * (n + e + f) + 3) + k0 + 2) + (k0 + 1) + 1 +
    (q * (2 * (n + e + f) + 3) + q + 2) + (q + 1)

set_option maxHeartbeats 1600000 in
/-- **Run of the precomputation (initial-row generator).** Let $L$ be a layout with $K$ stacks,
let $i_c$ and $k_0$ be natural numbers and let $y$ be a list of certificate codes. For all natural
numbers $T, n, e, f$ and every output $o$, the counter part of the generator for $L$, $i_c$,
$k_0$, $y$ runs within $\mathrm{preB}(L, k_0, K - k_0 - 1, T, n, e, f)$ steps, the step bound for
the precomputation (with truncated subtraction), from the label $\mathrm{eg}$ of the first
precomputation part (its first stage), with flag false, the initial counters for $T, n, e, f$ and
output $o$, to the loop head of the tail phase, with flag false, the counters after the
precomputation for $L, k_0, T, n, e, f$ and output $o$. -/
theorem pre_run (T n e f : ℕ) (o : List Bool) :
    RunLe (prog L ic k0 ycs) (preB L k0 (L.KK - k0 - 1) T n e f)
      ⟨some (.pre1 .eg), false, st (initF T n e f) o⟩
      ⟨some (.hd .tail), false, st (preF L k0 T n e f) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre1 .eg) (next := .pre1 .cpM1) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpM1) (l₂ := .pre1 .cpM2)
    (next := .pre1 .cpE1) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpE1) (l₂ := .pre1 .cpE2)
    (next := .pre1 .cpH1) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpH1) (l₂ := .pre1 .cpH2)
    (next := .pre1 .cpF1) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpF1) (l₂ := .pre1 .cpF2)
    (next := .pre1 (.hg .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _
    _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre1 (.hg s)) (next := .pre1 .wA)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre1 .wA) (next := .pre1 .wK) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre1 .wK) (next := .pre1 (.w .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre1 (.w s)) (next := .pre1 .wD)
    (a := .KA) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre1 .wD) (next := .pre1 .inc) (x := .KA) rfl _ _
    _).bud ?_
  refine (incS (M := prog L ic k0 ycs) (self := .pre1 .inc) (next := .pre1 (.v .head)) (x := .Tn)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre1 (.v s)) (next := .pre2 .zA)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .zA) (next := .pre2 .zK) (x := .ZA) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .zK) (next := .pre2 (.z .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.z s)) (next := .pre2 .zD)
    (a := .KA) (ad := .md) (b := .HG) (c := .ZA) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre2 .zD) (next := .pre2 .f1) (x := .KA) rfl _ _
    _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .f1) (l₂ := .pre2 .f2)
    (next := .pre2 (.f .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _
    _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.f s)) (next := .pre2 .s1)
    (a := .Xn) (ad := .md) (b := .Gc) (c := .Z45) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .s1) (l₂ := .pre2 .s2)
    (next := .pre2 (.s .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _
    _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.s s)) (next := .pre2 .z1)
    (a := .Mm) (ad := .md) (b := .Gc) (c := .Z6) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .z1) (next := .pre2 .t1) (x := .Z1) rfl _ _
    _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .t1) (l₂ := .pre2 .t2)
    (next := .pre2 .t3) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .t3) (l₂ := .pre2 .t4)
    (next := .pre2 .nK) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .nK) (next := .pre2 (.n .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.n s)) (next := .pre2 .nD)
    (a := .KA) (ad := .md) (b := .Hs) (c := .N1) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre2 .nD) (next := .pre2 .qK) (x := .KA) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .qK) (next := .pre2 (.q .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.q s)) (next := .pre2 .qD)
    (a := .KA) (ad := .md) (b := .Hs) (c := .N2) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre2 .qD) (next := .hd .tail) (x := .KA) rfl _ _
    _).bud ?_
  refine bud_st (F' := preF L k0 T n e f) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars, Layout.cIdx] <;>
      first | ring1 | (left; ring1)) (Bud.fin ?_ rfl)
  simp [initF, preB]
  ring_nf
  omega

end Top

/-- **The I3 loop on the whole input.** Let $L$ be a layout with $g$ symbol codes, consider the
init generator for a start code, a stack $k_0$ and a list of $\ell$ certificate codes, and let
$x = (x_0, \dots, x_{s-1})$ be a list of codes $x_j < g$. Suppose its counters $F$ have $Q$,
$\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$, $\mathrm{CB}$ and $P$ equal to $0$,
$\mathrm{Vc} = V$, $\mathrm{Gc} = g$, $\mathrm{ZA} = Z$ and $\mathrm{Xn} = s$, that
$jg + Z + g \le V$ for every $j < s$, and that $s \le N_b$. Then for every output $o$ and every
flag $v$, the generator, started at the head of the I3 loop with flag $v$, counters $F$, output
$o$, and $x_{s-1}, \dots, x_1, x_0$ on its input stack (top first), reaches in at most
$s\beta + 1$ steps the head of the I2 loop over the stacks above $k_0$, with flag false, the
counters of $F$ except $\mathrm{Xn} = 0$, an empty input stack, and output
$e_0 e_1 \cdots e_{s-1}$ followed by $o$. Here $e_j$ is the encoding of the dense clause over
$V$ variables whose only literal is the positive literal of variable $jg + Z + x_j$, and
$\beta = 3V^2 + 12V + (\ell + 2)(6V + 9) + (2g + 4)N_b + g + 10$. -/
theorem i3_full {L : Layout} {ic k0 : ℕ} {ycs : List ℕ} {V ZA Nb : ℕ} (xs : List (Fin L.g))
    (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0) (hP : F .P = 0) (hV : F .Vc = V)
    (hG : F .Gc = L.g) (hZA : F .ZA = ZA) (hX : F .Xn = xs.length)
    (hR : ∀ j < xs.length, j * L.g + ZA + L.g ≤ V) (hNb : xs.length ≤ Nb) (o : List Bool)
    (v : Bool) :
    RunLe (iprog L ic k0 ycs) (xs.length * bodyB (ycs.length + 2) L.g Nb V + 1)
      ⟨some .i3h, v, emb (st F o) xs.reverse⟩
      ⟨some (.hd .o2), false, emb (st (update F .Xn 0) ((List.range xs.length).flatMap
        (fun j => encodeClause (denseClause V
          [(j * L.g + ZA + (xs[j]?).elim 0 Fin.val, true)])) ++ o)) []⟩ := by
  have := i3_run (ic := ic) (k0 := k0) (ycs := ycs) xs F hF hCB hP hV hG hZA hR hNb xs.length
    le_rfl o v
  rwa [List.take_length,
    show update F .Xn xs.length = F from update_eq_self_iff.2 hX.symm] at this

/-! ## [FAM] The whole generator -/

section Gen

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

/-- **Step bound of one phase loop (initial-row generator).** For $m, g, N, V \in \mathbb{N}$,
the cost of one phase loop with count bound $N$ is $N(\beta + 1) + N + 2$, where $\beta$ is the
cost of one loop iteration with clauses of at most $m$ literals, $g$ symbol codes, count bound
$N$ and $V$ variables. -/
def loopB (nm g NB V : ℕ) : ℕ := NB * (bodyB nm g NB V + 1) + NB + 2

/-- **Time bound of the init generator.** Let $L$ be a layout with $A$ label/state variables,
$K$ stacks and $g$ symbol codes, and let $n_Y, k_0, q, T, n, e, f$ be natural numbers. Put
$H = n + e + f$ and let $V = (T + 1)(A + K H g)$ be the number of variables. The bound is the
precomputation cost $\mathrm{preB}(L, k_0, q, T, n, e, f)$, plus $6$ times the phase-loop cost
$\mathrm{loopB}(n_Y + 2, g, K H + H, V)$, plus the clause cost $\mathrm{clauseB}(n_Y + 2, V)$.

The generator uses it with $q = K - k_0 - 1$. -/
def initBound (L : Layout) (nY k0 q T n e f : ℕ) : ℕ :=
  preB L k0 q T n e f +
    6 * loopB (nY + 2) L.g (L.KK * (n + e + f) + (n + e + f)) (L.numVars T (n + e + f)) +
    clauseB (nY + 2) (L.numVars T (n + e + f))

theorem shiftC (H k j t : ℕ) : t * L.g + L.cIdx H 0 k j 0 = L.A + (k * H + (j + t)) * L.g := by
  rw [cIdx0]; ring1

theorem enc_initFam (hk0 : k0 < L.KK) (xs : List (Fin L.g)) (e f T : ℕ) :
    encodeCNF (initFam L ic k0 ycs xs (xs.length + e) T (xs.length + e + f)) =
      encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs 0 (CL.code : CL L.g ycs.length))) ++
      ((List.range (k0 * (xs.length + e + f))).flatMap (fun t => encodeClause
          (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.A) (CL.ph .o1 : CL L.g ycs.length)))) ++
      ((List.range ((L.KK - k0 - 1) * (xs.length + e + f))).flatMap (fun t => encodeClause
          (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 (k0 + 1) 0 0)
            (CL.ph .o2 : CL L.g ycs.length)))) ++
      ((List.range xs.length).flatMap (fun j => encodeClause
          (denseClause (L.numVars T (xs.length + e + f))
          [(j * L.g + L.cIdx (xs.length + e + f) 0 k0 0 0 + (xs[j]?).elim 0 Fin.val, true)])) ++
      ((List.range e).flatMap (fun t => encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 k0 xs.length 0)
            (CL.ph .cert : CL L.g ycs.length)))) ++
      ((List.range e).flatMap (fun t => encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 k0 xs.length 0)
            (CL.ph .pre : CL L.g ycs.length)))) ++
      (List.range f).flatMap (fun t => encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 k0 (xs.length + e) 0)
            (CL.ph .tail : CL L.g ycs.length))))))))) := by
  have hfa : ∀ a b : CNF, encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b :=
    fun a b => List.flatMap_append
  rw [initFam, hfa, hfa, hfa, hfa, hfa, enc_code (ycs := ycs),
      enc_other (ic := ic) (ycs := ycs) hk0,
    enc_in, enc_cert (ic := ic), enc_pre (ic := ic) (ycs := ycs),
    enc_tail (ic := ic) (ycs := ycs), Nat.add_sub_cancel_left,
    show xs.length + e + f - (xs.length + e) = f by omega]
  simp only [List.append_assoc]

/-- **Correctness of the init generator, with its explicit time bound.** Let $L$ be a layout with
$A$ label/state variables, $K$ stacks and $g > 0$ symbol codes, let $i_c < A$ and $k_0 < K$, and
let $Y$ be a strictly increasing list of codes with $0 < y < g$ for every $y \in Y$. Let $xs$ be a
list of codes below $g$ with $n = |xs|$, let $T, e, f$ be natural numbers with $f > 0$, and let
$o$ be a bit string. Start the generator for $L, i_c, k_0, Y$ at its start label with state false,
with the counters $\mathrm{Tn}, \mathrm{Xn}, \mathrm{En}, \mathrm{Fn}$ holding $T, n, e, f$ in
unary and all other counters empty, $o$ on the output stack, and $xs$ reversed on the input
stack. Then within $\mathrm{initBound}(L, |Y|, k_0, K - k_0 - 1, T, n, e, f)$ steps it reaches
the final label $\mathrm{done}$, and its output stack there is the bit encoding of the
layout-level init family for $L, i_c, k_0, Y, xs$, $m = n + e$, $T$ and $H = n + e + f$, followed
by $o$. -/
theorem init_run (hk0 : k0 < L.KK) (hic : ic < L.A) (hg : 0 < L.g)
    (hy : (0 :: ycs).Pairwise (· < ·)) (hyg : ∀ c ∈ ycs, c < L.g) (xs : List (Fin L.g))
    (T e f : ℕ) (hf : 0 < f) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin L.g) k)),
      RunLe (iprog L ic k0 ycs) (initBound L ycs.length k0 (L.KK - k0 - 1) T xs.length e f)
        ⟨some (.pre1 .eg), false, emb (st (initF T xs.length e f) o) xs.reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (initFam L ic k0 ycs xs (xs.length + e) T (xs.length + e + f)) ++ o := by
  have lf := lifts L ic k0 ycs
  have hR0 : Rest (preF L k0 T xs.length e f) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hR1 : Rest (update (preF L k0 T xs.length e f) .Xn 0) :=
    hR0.upd (by decide) (by decide) (by decide) (by decide) (by decide) 0
  -- positions: every row-0 cell base `A + q·g` with `q < KK·H` leaves room for `g` codes
  have posA : ∀ k j, k < L.KK → j < xs.length + e + f →
      L.A + (k * (xs.length + e + f) + j) * L.g + L.g ≤ L.numVars T (xs.length + e + f) :=
    fun k j hk hj => qpos (kq_lt hk hj)
  have hAV : L.A ≤ L.numVars T (xs.length + e + f) := by
    unfold Layout.numVars Layout.rowW
    exact le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hNB : xs.length + e + f ≤ L.KK * (xs.length + e + f) + (xs.length + e + f) :=
    Nat.le_add_left _ _
  have hk2 : (k0 + 1) * (xs.length + e + f) + (L.KK - k0 - 1) * (xs.length + e + f) =
      L.KK * (xs.length + e + f) := by rw [← Nat.add_mul]; congr 1; omega
  have hk1 : k0 * (xs.length + e + f) ≤ L.KK * (xs.length + e + f) :=
    Nat.mul_le_mul_right _ hk0.le
  refine ⟨false, ?_⟩
  apply Exists.intro
  refine And.intro ?run ?eq
  case run =>
    refine Bud.start ((runLe_lift lf xs.reverse
      (pre_run (ic := ic) (ycs := ycs) T xs.length e f o)).bud ?_)
    -- I6
    refine (runLe_lift lf xs.reverse (phase_run (p := .tail) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR0 rfl rfl rfl
      rfl rfl rfl rfl (by first | omega | (simp only [PH.cN, preF]; omega)) (wf_unit rfl)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + e + t) hk0 (by omega)
        omega)
      (fun t ht => inr_unit rfl (by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢; simp only [CL.off]; rw [Nat.add_zero, shiftC]
        have := posA k0 (xs.length + e + t) hk0 (by omega)
        omega)) _ _)).bud ?_
    -- I5
    refine (runLe_lift lf xs.reverse (phase_run (p := .pre) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR0 rfl rfl rfl
      rfl rfl rfl rfl (by first | omega | (simp only [PH.cN, preF]; omega)) (wf_pre hg)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + t) hk0 (by omega)
        omega)
      (fun t ht => inr_pre (by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢; rw [shiftC]
        have := posA k0 (xs.length + t + 1) hk0 (by omega)
        have e1 : (k0 * (xs.length + e + f) + (xs.length + t + 1)) * L.g =
            (k0 * (xs.length + e + f) + (xs.length + t)) * L.g + L.g := by ring1
        omega)) _ _)).bud ?_
    -- I4
    refine (runLe_lift lf xs.reverse (phase_run (p := .cert) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR0 rfl rfl rfl
      rfl rfl rfl rfl (by first | omega | (simp only [PH.cN, preF]; omega)) (wf_cert hy)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + t) hk0 (by omega)
        omega)
      (fun t ht => inr_cert hyg (by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + t) hk0 (by omega)
        omega) hg) _ _)).bud ?_
    -- I3 (reads the input)
    refine (i3_full (ic := ic) (k0 := k0) (ycs := ycs) xs _ hR0 rfl rfl rfl rfl rfl rfl
      (fun j hj => by
        simp only [preF]; rw [shiftC]; have := posA k0 (0 + j) hk0 (by omega)
        omega) (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) (by omega) _ _).bud ?_
    -- I2, stacks above `k0`
    refine (runLe_lift lf [] (phase_run (p := .o2) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR1 rfl rfl rfl
      rfl rfl rfl rfl (by simp only [PH.cN, preF, update_apply]; simp; omega) (wf_unit rfl)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, ite_false] at ht ⊢
        rw [shiftC]; have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := (k0 + 1) * (xs.length + e + f) + (0 + t))
          (by omega)
        omega)
      (fun t ht => inr_unit rfl (by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, ite_false] at ht ⊢
        simp only [CL.off]; rw [Nat.add_zero, shiftC]
        have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := (k0 + 1) * (xs.length + e + f) + (0 + t)) (by omega)
        omega)) _ _)).bud ?_
    -- I2, stacks below `k0`
    refine (runLe_lift lf [] (phase_run (p := .o1) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR1 rfl rfl rfl
      rfl rfl rfl rfl (by simp only [PH.cN, preF, update_apply]; simp; omega) (wf_unit rfl)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, ite_false] at ht ⊢
        have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := t) (by omega)
        omega)
      (fun t ht => inr_unit rfl (by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, ite_false] at ht ⊢
        simp only [CL.off]
        have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := t) (by omega)
        omega)) _ _)).bud ?_
    -- I1
    refine (runLe_lift lf [] (clause_run (k0 := k0) (c := (CL.code : CL L.g ycs.length)) (B := 0)
      (wf_unit rfl) (inr_unit rfl (by simp [CL.off, preF]; omega)) _ hR1 rfl rfl rfl _ _)).bud ?_
    refine Bud.fin ?_ rfl
    have h3 : xs.length * bodyB (ycs.length + 2) L.g (L.KK * (xs.length + e + f) +
        (xs.length + e + f)) (L.numVars T (xs.length + e + f)) ≤
        (L.KK * (xs.length + e + f) + (xs.length + e + f)) * (bodyB (ycs.length + 2) L.g
          (L.KK * (xs.length + e + f) + (xs.length + e + f)) (L.numVars T (xs.length + e + f)) + 1) :=
      Nat.mul_le_mul (by omega) (Nat.le_succ _)
    unfold initBound loopB
    simp only [preF, update_apply, reduceCtorEq, ite_false]
    omega
  case eq =>
    rw [enc_initFam (ic := ic) (ycs := ycs) hk0 xs e f T]
    simp only [emb_b, st_out, preF, PH.cZ, PH.cN, update_apply, reduceCtorEq, ite_false,
      List.append_assoc]

end Gen

/-! ## [BOUND] The time bound is polynomial: `initBound ≤ initC · (T + H + 1)^5` -/

section Poly

theorem initBound_mono {L L' : Layout} {nY nY' k0 k0' q q' T T' n n' e e' f f' : ℕ}
    (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK) (hg : L.g ≤ L'.g) (hnY : nY ≤ nY') (hk : k0 ≤ k0')
    (hq : q ≤ q') (hT : T ≤ T') (hn : n ≤ n') (he : e ≤ e') (hf : f ≤ f') :
    initBound L nY k0 q T n e f ≤ initBound L' nY' k0' q' T' n' e' f' := by
  unfold initBound preB loopB bodyB clauseB litE Layout.numVars Layout.rowW
  gcongr

/-- **Time bound of the init generator at uniform parameters.** For all natural numbers $k \ge 1$
and $y \ge 1$, let $L$ be the uniform layout with all four parameters equal to $k$. Then the time
bound of the init generator for $L$ with $n_Y = k_0 = q = k$ and $T = n = e = f = y$ is at most
$18928\,k^5 y^5$.

Every monomial of the bound is then at most $k^5 y^5$, and $18928$ is the value of the bound at
$k = y = 1$. -/
theorem initBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    initBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k k k y y y y ≤ 18928 * k ^ 5 * y ^ 5 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 5 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 5 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold initBound preB loopB bodyB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  ring_nf
  linarith [m 0 0 (by norm_num) (by norm_num), m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num), m 0 3 (by norm_num) (by norm_num),
    m 0 4 (by norm_num) (by norm_num), m 0 5 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num), m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num), m 1 3 (by norm_num) (by norm_num),
    m 1 4 (by norm_num) (by norm_num), m 1 5 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num), m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num), m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num), m 2 5 (by norm_num) (by norm_num),
    m 3 0 (by norm_num) (by norm_num), m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num), m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num), m 3 5 (by norm_num) (by norm_num),
    m 4 0 (by norm_num) (by norm_num), m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num), m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num), m 4 5 (by norm_num) (by norm_num),
    m 5 0 (by norm_num) (by norm_num), m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num), m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num), m 5 5 (by norm_num) (by norm_num)]

/-- The constant 18928 is exact: the sum of the coefficients. -/
example : initBound (Cslib.Complexity.CookLevin.Family.Layout.uni 1) 1 1 1 1 1 1 1 = 18928 := rfl

/-- **Constant of the init generator's time bound.** For a layout $L$ with $A$ label/state
variables, $K$ stacks and $g$ symbol codes, and natural numbers $n_Y$ and $k_0$, the constant is
$18928\,(A + K + g + n_Y + k_0 + 1)^5$.

It depends only on $A$, $K$, $g$, the number $n_Y$ of certificate codes and the input stack
$k_0$. -/
def initC (L : Layout) (nY k0 : ℕ) : ℕ := 18928 * (L.A + L.KK + L.g + nY + k0 + 1) ^ 5

theorem initBound_le (L : Layout) (nY k0 T n e f : ℕ) :
    initBound L nY k0 (L.KK - k0 - 1) T n e f ≤ initC L nY k0 * (T + (n + e + f) + 1) ^ 5 := by
  have := initBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + nY + k0 + 1))
    (nY := nY) (k0 := k0) (q := L.KK - k0 - 1) (T := T) (n := n) (e := e) (f := f)
    (nY' := L.A + L.KK + L.g + nY + k0 + 1) (k0' := L.A + L.KK + L.g + nY + k0 + 1)
    (q' := L.A + L.KK + L.g + nY + k0 + 1)
    (T' := T + (n + e + f) + 1) (n' := T + (n + e + f) + 1) (e' := T + (n + e + f) + 1)
    (f' := T + (n + e + f) + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have h2 := initBound_uni (L.A + L.KK + L.g + nY + k0 + 1) (T + (n + e + f) + 1) (by omega)
    (by omega)
  unfold initC
  exact this.trans h2

/-- **Polynomial time bound for the init generator.** Let $L$ be a layout with $A$ label/state
variables, $K$ stacks and $g > 0$ symbol codes, let $i_c < A$ and $k_0 < K$, and let $Y$ be a
strictly increasing list of codes with $0 < y < g$ for every $y \in Y$. Let $xs$ be a list of
codes below $g$ with $n = |xs|$, let $T, e, f$ be natural numbers with $f > 0$, and let $o$ be a
bit string. Start the generator for $L, i_c, k_0, Y$ at its start label with state false, with
the counters $\mathrm{Tn}, \mathrm{Xn}, \mathrm{En}, \mathrm{Fn}$ holding $T, n, e, f$ in unary
and all other counters empty, $o$ on the output stack, and $xs$ reversed on the input stack.
Then within $C\,(T + n + e + f + 1)^5$ steps, where $C = 18928\,(A + K + g + |Y| + k_0 + 1)^5$,
it reaches the final label $\mathrm{done}$, and its output stack there is the bit encoding of the
layout-level init family for $L, i_c, k_0, Y, xs$, $m = n + e$, $T$ and $H = n + e + f$, followed
by $o$. -/
theorem init_time {L : Layout} {ic k0 : ℕ} {ycs : List ℕ} (hk0 : k0 < L.KK) (hic : ic < L.A)
    (hg : 0 < L.g) (hy : (0 :: ycs).Pairwise (· < ·)) (hyg : ∀ c ∈ ycs, c < L.g)
    (xs : List (Fin L.g)) (T e f : ℕ) (hf : 0 < f) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin L.g) k)),
      RunLe (iprog L ic k0 ycs)
        (initC L ycs.length k0 * (T + (xs.length + e + f) + 1) ^ 5)
        ⟨some (.pre1 .eg), false, emb (st (initF T xs.length e f) o) xs.reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (initFam L ic k0 ycs xs (xs.length + e) T (xs.length + e + f)) ++ o :=
  let ⟨v, S, h, h'⟩ := init_run hk0 hic hg hy hyg xs T e f hf o
  ⟨v, S, h.mono (initBound_le L ycs.length k0 T xs.length e f), h'⟩

end Poly

/-! ## [FAM] Link to the semantic family `Situation.Enc.initFamily` (I4 sorted and deduplicated) -/

section Link

/-- **Lookup in an all-positive literal list.** Let $\lambda$ be a list of pairs of a natural
number and a boolean in which every boolean is true. For every $v \in \mathbb{N}$, looking up $v$
in $\lambda$ (the boolean of the first pair with first entry $v$, if any) gives true if $v$ is
the first entry of some pair in $\lambda$, and no value otherwise. -/
theorem lookup_pos (v : ℕ) : ∀ ls : List (ℕ × Bool), (∀ p ∈ ls, p.2 = true) →
    ls.lookup v = if v ∈ ls.map Prod.fst then some true else none
  | [], _ => by simp [List.lookup]
  | (p, b) :: r, h => by
    have hb : b = true := h (p, b) (List.mem_cons_self ..)
    subst hb
    have ih := lookup_pos v r (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hv : v = p
    · subst hv; simp [List.lookup]
    · simp only [List.lookup, List.map_cons, List.mem_cons, hv, false_or]
      rw [show (v == p) = false from by simpa using hv]
      exact ih

/-- **Dense clauses of positive literals depend only on their positions.** Let $\ell$ and
$\ell'$ be lists of literals (pairs of a position and a sign) in which every sign is positive. If
every natural number $v$ is a position of $\ell$ exactly when it is a position of $\ell'$, then
for every $V$ the dense clause over $V$ variables with literals $\ell$ equals the dense clause
over $V$ variables with literals $\ell'$: order and repetitions in the lists are irrelevant. -/
theorem denseClause_congr {V : ℕ} {ls ls' : List (ℕ × Bool)} (h : ∀ p ∈ ls, p.2 = true)
    (h' : ∀ p ∈ ls', p.2 = true) (hm : ∀ v, v ∈ ls.map Prod.fst ↔ v ∈ ls'.map Prod.fst) :
    denseClause V ls = denseClause V ls' := by
  unfold denseClause
  congr 1; funext v
  rw [lookup_pos v ls h, lookup_pos v ls' h']
  simp only [hm v]

variable {M : FinTM2} (E : Cslib.Complexity.CookLevin.Situation.Enc M)

/-- **Sorted certificate code list.** Given an encoding $E$ of a machine $M$ and a list $Y$ of
symbols of the input stack of $M$, this is the list of the distinct codes that $E$ assigns to the
symbols of $Y$ on the input stack, sorted in strictly increasing order.

Besides the empty cell, these are the codes allowed in the certificate cells of the initial row
(clause group I4). -/
noncomputable def ycs (Ys : List (M.Γ M.k₀)) : List ℕ :=
  ((Ys.map (E.enc M.k₀)).toFinset).sort (· ≤ ·)

/-- **Codes of input symbols.** Let $E$ be an encoding of a finite multi-stack Turing machine $M$,
and let $g$ be the number of symbol codes of the layout of $E$. A symbol $z$ of the input stack
of $M$ is sent to its symbol code under $E$, viewed as an element of $\{0, \dots, g - 1\}$; the
code is below $g$ because every input symbol is an effective symbol of the input stack. -/
def encF (z : M.Γ M.k₀) : Fin E.layout.g := ⟨E.enc M.k₀ z, E.enc_lt _ z (E.input_mem z)⟩

theorem mem_ycs (Ys : List (M.Γ M.k₀)) (c : ℕ) : c ∈ ycs E Ys ↔ ∃ z ∈ Ys, E.enc M.k₀ z = c := by
  simp [ycs]

theorem enc_pos (z : M.Γ M.k₀) : 0 < E.enc M.k₀ z := by
  obtain ⟨i, rfl⟩ := E.input_mem z
  rw [E.enc_dec]; omega

theorem ycs_ok (Ys : List (M.Γ M.k₀)) :
    (0 :: ycs E Ys).Pairwise (· < ·) ∧ ∀ c ∈ ycs E Ys, c < E.layout.g := by
  have hs : (ycs E Ys).Pairwise (· < ·) := List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _)
  refine ⟨List.pairwise_cons.2 ⟨fun c hc => ?_, hs⟩, fun c hc => ?_⟩
  · obtain ⟨z, -, rfl⟩ := (mem_ycs E Ys c).1 hc; exact enc_pos E z
  · obtain ⟨z, -, rfl⟩ := (mem_ycs E Ys c).1 hc; exact E.enc_lt _ z (E.input_mem z)

/-- **The init family of an encoding is a layout-level init family.** Let $E$ be an encoding of a
machine $M$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and let $m, T, H$ be
natural numbers. The init family of $E$ for $x, Y, m, T, H$ equals the layout-level init family
over the layout of $E$ with start code the code of the pair of the main label and the initial
state of $M$, stack $k_0$ the number of the input stack, code list the codes of the symbols of $Y$
in increasing order without repetitions, input codes the codes of the symbols of $x$, and the
same $m, T, H$.

The family of $E$ lists the certificate symbols $Y$ in their given order, possibly with repeated
codes; the equality holds because order and repetitions do not change these clauses. -/
theorem initFamily_eq (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) :
    E.initFamily x Ys m T H =
      initFam E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (ycs E Ys)
        (x.map (encF E)) m T H := by
  have hI : E.initIn x T H = iIn E.layout (E.kc M.k₀) (x.map (encF E)) T H := by
    unfold Cslib.Complexity.CookLevin.Situation.Enc.initIn iIn
    rw [List.length_map]
    congr 1; funext j
    rw [List.getElem?_map]
    cases x[j]? <;> rfl
  have hC : E.initCert x Ys m T H = iCert E.layout (E.kc M.k₀) (ycs E Ys) (x.map (encF E)).length m T H := by
    unfold Cslib.Complexity.CookLevin.Situation.Enc.initCert iCert
    rw [List.length_map]
    congr 1; funext i
    refine denseClause_congr ?_ ?_ (fun v => ?_)
    · intro p hp; simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨z, -, rfl⟩ <;> rfl
    · intro p hp; simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨c, -, rfl⟩ <;> rfl
    · simp only [List.map_cons, List.mem_cons, List.map_map, List.mem_map, Function.comp_def,
        mem_ycs]
      constructor
      · rintro (h | ⟨z, hz, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      · rintro (h | ⟨c, ⟨z, hz, rfl⟩, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨z, hz, rfl⟩
  have hP : E.initPre x m T H = iPre E.layout (E.kc M.k₀) (x.map (encF E)).length m T H := by
    rw [List.length_map]; rfl
  unfold Cslib.Complexity.CookLevin.Situation.Enc.initFamily initFam
  rw [hI, hC, hP, List.length_map]
  rfl

/-- **Time and output of the init generator for an encoding.** Let $E$ be an encoding of a
machine $M$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let $m, T, H$ be
natural numbers with $|x| \le m < H$, and let $o$ be a bit string. Let $C$ be the time constant
for the layout of $E$, the number of distinct codes of $Y$ and the number $k_0$ of the input
stack. Start the generator for $E$ (start code: the code of the pair of the main label and the
initial state; stack $k_0$; code list: the distinct codes of $Y$ in increasing order) at its
start label with state false, with the counters $\mathrm{Tn}, \mathrm{Xn}, \mathrm{En},
\mathrm{Fn}$ holding $T$, $|x|$, $m - |x|$, $H - m$ in unary and all other counters empty, $o$
on the output stack, and the list of codes of $x$, reversed, on the input stack. Then within
$C\,(T + H + 1)^5$ steps it reaches the final label $\mathrm{done}$, and its output stack there
is the bit encoding of the init family of $E$ for $x, Y, m, T, H$ followed by $o$. -/
theorem init_gen_time (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) (hx : x.length ≤ m) (hmH : m < H)
    (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin E.layout.g) k)),
      RunLe (iprog E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (ycs E Ys))
        (initC E.layout (ycs E Ys).length (E.kc M.k₀) * (T + H + 1) ^ 5)
        ⟨some (.pre1 .eg), false,
          emb (st (initF T x.length (m - x.length) (H - m)) o) (x.map (encF E)).reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (E.initFamily x Ys m T H) ++ o := by
  obtain ⟨hy, hyg⟩ := ycs_ok E Ys
  have hg : 0 < E.layout.g := by show 0 < E.g; unfold Cslib.Complexity.CookLevin.Situation.Enc.g; omega
  have hic : E.lc (some M.main, M.initialState) < E.layout.A :=
    lt_of_lt_of_le (E.lc_lt _) (Nat.le_add_right _ _)
  obtain ⟨v, S, h, h'⟩ := init_time (ic := E.lc (some M.main, M.initialState)) (E.kc_lt M.k₀) hic hg
    hy hyg (x.map (encF E)) T (m - x.length) (H - m) (by omega) o
  rw [List.length_map] at h h'
  have e1 : x.length + (m - x.length) = m := by omega
  have e2 : x.length + (m - x.length) + (H - m) = H := by omega
  rw [e2] at h
  rw [e1, show m + (H - m) = H by omega, ← initFamily_eq E] at h'
  exact ⟨v, S, h, h'⟩

/-- **The init generator at the stack cap.** Let $E$ be an encoding of a machine $M$ with window
depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let $m, T$ be natural
numbers with $|x| \le m$, let $H = m + (T + 1)d + 1$ be the stack cap, and let $o$ be a bit
string. Let $C$ be the time constant for the layout of $E$, the number of distinct codes of $Y$
and the number $k_0$ of the input stack. Start the generator for $E$ (start code: the code of
the pair of the main label and the initial state; stack $k_0$; code list: the distinct codes of
$Y$ in increasing order) at its start label with state false, with the counters $\mathrm{Tn},
\mathrm{Xn}, \mathrm{En}, \mathrm{Fn}$ holding $T$, $|x|$, $m - |x|$, $H - m$ in unary and all
other counters empty, $o$ on the output stack, and the list of codes of $x$, reversed, on the
input stack. Then within $C\,(T + H + 1)^5$ steps it reaches the final label $\mathrm{done}$,
and its output stack there is the bit encoding of the init family of $E$ for $x, Y, m, T, H$
followed by $o$. -/
theorem init_gen_capH (x Ys : List (M.Γ M.k₀)) (m T : ℕ) (hx : x.length ≤ m) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin E.layout.g) k)),
      RunLe (iprog E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (ycs E Ys))
        (initC E.layout (ycs E Ys).length (E.kc M.k₀) *
          (T + Cslib.Complexity.CookLevin.Situation.capH m T (Cslib.Complexity.CookLevin.Situation.depth M) + 1) ^ 5)
        ⟨some (.pre1 .eg), false, emb (st (initF T x.length (m - x.length)
          (Cslib.Complexity.CookLevin.Situation.capH m T (Cslib.Complexity.CookLevin.Situation.depth M) - m)) o) (x.map (encF E)).reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (E.initFamily x Ys m T (Cslib.Complexity.CookLevin.Situation.capH m T (Cslib.Complexity.CookLevin.Situation.depth M))) ++ o :=
  init_gen_time E x Ys m T _ hx (by unfold Cslib.Complexity.CookLevin.Situation.capH; omega) o

end Link

end Cslib.Complexity.CookLevin.InitFamily
