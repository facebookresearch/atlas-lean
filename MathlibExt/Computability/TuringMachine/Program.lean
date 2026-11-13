/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Prog.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Prog.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`MetaMathlibExt` namespaces, `iter_none` (from `Emb.lean`/`Comp.lean`) added as the shared copy.
-/

module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.List.Sigma

/-!
# A program library for `TM2` machines

Generic building blocks for writing `Turing.TM2` machines by hand, each with an **exact** step
count:

* `Run M n c d`: `n` steps of `M` lead from `c` to `d`; sequencing is `Run.trans`.
* unary counters: the value `n` on stack `k` is `List.replicate n u`, stack `k` holding nothing
  else;
* `incr`, `decr`: one step each;
* `xfer`: pop a counter to empty and push a copy onto every target (drain / move / copy);
* `cmp`: non-destructive three-way comparison of two counters;
* `forLoop`: iterate a body once per unit of a counter, with the loop index kept on a stack;
* `emit`: push a constant list of symbols.

Machines are arbitrary `M : Λ → TM2.Stmt Γ Λ σ` with dependent alphabets `Γ : K → Type`.
A primitive occupies some labels of `Λ`; its lemma takes hypotheses `M l = …` for those labels
(discharged by `rfl` for a concrete machine). Branching on "was the pop empty?" needs one bit of
state, provided by `[Flag σ]`.

The library is used by the Cook-Levin port (SAT verifier and clause generators) and by the stack
embedding in `MathlibExt.Computability.TuringMachine.StackEmbedding`.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Program

open Turing Function

/-- **Flag bit of a machine state.** A flag on a type $\sigma$ of machine states consists of a map
$\mathrm{tag} : \mathrm{Bool} \to \sigma$ that stores a bit in a state and a map
$\mathrm{untag} : \sigma \to \mathrm{Bool}$ that reads it back, such that
$\mathrm{untag}(\mathrm{tag}(\beta)) = \beta$ for every bit $\beta$. The program primitives use it
to branch on whether a pop found a symbol. -/
class Flag (σ : Type) where
  /-- Store a bit in the state. -/
  tag : Bool → σ
  /-- Read the stored bit back. -/
  untag : σ → Bool
  /-- Reading back what was stored. -/
  untag_tag : ∀ b, untag (tag b) = b

instance : Flag Bool := ⟨id, id, fun _ => rfl⟩

attribute [simp] Flag.untag_tag

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-! ### Runs and sequencing -/

/-- **A halted run stays halted.** Let $f : \sigma \to \mathrm{Option}\,\sigma$ be a partial step
function and let $\hat f$ be its lift to $\mathrm{Option}\,\sigma$, which sends $\mathrm{none}$ to
$\mathrm{none}$ and $\mathrm{some}\,x$ to $f(x)$. Then $\hat f^{\,n}(\mathrm{none}) = \mathrm{none}$
for every $n \in \mathbb{N}$. -/
theorem iter_none {σ : Type} (f : σ → Option σ) (n : ℕ) : (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply]; exact ih

section Run

variable (M : Λ → TM2.Stmt Γ Λ σ)

/-- **Exact-length runs of a TM2 machine.** Let $M$ be a TM2 machine, given by a statement for
each label, and let $c$ and $d$ be configurations. For $n \in \mathbb{N}$, $M$ runs from $c$ to
$d$ in exactly $n$ steps when applying the step function of $M$ $n$ times, starting at $c$, is
defined at every step (no configuration before the last one has halted) and ends at $d$. -/
def Run (n : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  (flip bind (TM2.step M))^[n] (some c) = some d

variable {M}

theorem Run.zero (c : TM2.Cfg Γ Λ σ) : Run M 0 c c := rfl

theorem Run.head {n : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : TM2.step M c = some d)
    (h₂ : Run M n d e) : Run M (n + 1) c e := by
  unfold Run
  rw [iterate_succ_apply]
  exact (congrArg _ h₁).trans h₂

theorem Run.trans {n m : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : Run M n c d) (h₂ : Run M m d e) :
    Run M (n + m) c e := by
  unfold Run at *
  rw [add_comm, iterate_add_apply, h₁, h₂]

theorem Run.of_eq {n m : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) (hn : n = m) :
    Run M m c d := hn ▸ h

/-- **A single step executes the statement at the current label.** Let $M$ be a TM2 machine, $l$
a label, $v$ an internal state, $S$ an assignment of a list of symbols to each stack, and $d$ a
configuration. If executing the statement $M(l)$ from state $v$ and stacks $S$ yields $d$, then
$M$ runs in exactly one step from the configuration with label $l$, state $v$ and stacks $S$ to
$d$. -/
theorem Run.single {l : Λ} {v : σ} {S : ∀ k, List (Γ k)} {d : TM2.Cfg Γ Λ σ}
    (h : TM2.stepAux (M l) v S = d) : Run M 1 ⟨some l, v, S⟩ d :=
  Run.head (by simp [TM2.step, h]) (Run.zero _)

end Run

/-! ### Unary counters -/

/-- **Unary counter.** The unary counter with unit symbol $u$ and value $n \in \mathbb{N}$ is the
list $u^n$ consisting of exactly $n$ copies of $u$. -/
abbrev cnt {α : Type} (u : α) (n : ℕ) : List α := List.replicate n u

theorem cnt_length {α : Type} (u : α) (n : ℕ) : (cnt u n).length = n :=
  List.length_replicate

theorem cnt_succ {α : Type} (u : α) (n : ℕ) : cnt u (n + 1) = u :: cnt u n := rfl

@[simp] theorem cnt_zero {α : Type} (u : α) : cnt u 0 = [] := rfl

theorem cnt_add {α : Type} (u : α) (m n : ℕ) : cnt u m ++ cnt u n = cnt u (m + n) :=
  List.replicate_add m n u |>.symm

theorem cnt_injective {α : Type} (u : α) : Injective (cnt u) := fun m n h => by
  simpa using congrArg List.length h

/-! ### Increment and decrement -/

section IncDec

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Counter increment.** For a stack $k$, a symbol $u$ of stack $k$ (the unit of a unary
counter) and a label $\ell$, this statement pushes $u$ onto stack $k$ and then goes to label
$\ell$. -/
def incr (k : K) (u : Γ k) (next : Λ) : TM2.Stmt Γ Λ σ :=
  .push k (fun _ => u) (.goto fun _ => next)

/-- **Decrement.** For a stack $k$ and labels $\ell_0$ and $\ell_+$, this machine statement pops
stack $k$, stores in the state whether a symbol was popped, and goes to $\ell_+$ if a symbol was
popped and to $\ell_0$ if stack $k$ was empty. -/
def decr (k : K) (ifZero ifPos : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (.goto fun _ => ifPos) (.goto fun _ => ifZero))

omit [Flag σ] in
theorem incr_run {self next : Λ} {k : K} {u : Γ k} (hp : M self = incr k u next) (v : σ)
    (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (u :: S k)⟩ :=
  Run.single (by simp [hp, incr, TM2.stepAux])

omit [Flag σ] in
theorem incr_run_cnt {self next : Λ} {k : K} {u : Γ k} (hp : M self = incr k u next) (v : σ)
    {S : ∀ k, List (Γ k)} {n : ℕ} (hS : S k = cnt u n) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (cnt u (n + 1))⟩ := by
  simpa [hS, cnt_succ] using incr_run hp v S

theorem decr_run_pos {self ifZero ifPos : Λ} {k : K} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} {x : Γ k} {r : List (Γ k)} (hS : S k = x :: r) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifPos, Flag.tag true, update S k r⟩ :=
  Run.single (by simp [hp, decr, TM2.stepAux, hS])

theorem decr_run_cnt {self ifZero ifPos : Λ} {k : K} {u : Γ k} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} {n : ℕ} (hS : S k = cnt u (n + 1)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifPos, Flag.tag true, update S k (cnt u n)⟩ :=
  decr_run_pos hp v hS

theorem decr_run_zero {self ifZero ifPos : Λ} {k : K} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} (hS : S k = []) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifZero, Flag.tag false, S⟩ := by
  refine Run.single ?_
  have hu : update S k [] = S := by rw [← hS, update_eq_self]
  simp only [hp, decr, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, List.tail_nil, hu,
    Flag.untag_tag, Bool.cond_false]

end IncDec

/-! ### Transfer: drain, move, copy -/

section Xfer

/-- **Pushing symbols onto several stacks.** Let $ps$ be a list of pairs $(k, x)$ of a stack index
$k$ and a symbol $x$ of the alphabet of stack $k$, and let $q$ be a statement of a TM2 machine.
This is the statement that, for each pair $(k, x)$ of $ps$ in list order, pushes $x$ onto stack
$k$, and then continues with $q$. -/
def pushAll (ps : List (Σ k, Γ k)) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  ps.foldr (fun p q => .push p.1 (fun _ => p.2) q) q

/-- **Adding units to target stacks.** Let $ps$ be a list of pairs $(j, x)$ of a stack $j$ and a
symbol $x$ of stack $j$, let $i \in \mathbb{N}$ and let $S$ be stacks. The resulting stacks are
as follows: if $(k, x)$ is the first pair in $ps$ whose stack is $k$, stack $k$ holds $i$ copies
of $x$ followed by $S_k$ (so the copies are on top); if no pair in $ps$ has stack $k$, stack $k$
holds $S_k$.

When the stacks in the pairs of $ps$ are distinct, the first pair with stack $k$ is the only one. -/
def addU (ps : List (Σ k, Γ k)) (i : ℕ) (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) :=
  fun k => (List.dlookup k ps).elim (S k) (fun x => cnt x i ++ S k)

theorem addU_zero (ps : List (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : addU ps 0 S = S := by
  funext k; unfold addU; cases List.dlookup k ps <;> rfl

theorem addU_addU (ps : List (Σ k, Γ k)) (i j : ℕ) (S : ∀ k, List (Γ k)) :
    addU ps i (addU ps j S) = addU ps (i + j) S := by
  funext k; unfold addU
  cases List.dlookup k ps <;> simp [← List.append_assoc]

theorem addU_of_not_mem {ps : List (Σ k, Γ k)} {k : K} (hk : k ∉ ps.keys) (i : ℕ)
    (S : ∀ k, List (Γ k)) : addU ps i S k = S k := by
  simp [addU, List.dlookup_eq_none.2 hk]

theorem addU_update {ps : List (Σ k, Γ k)} {k : K} (hk : k ∉ ps.keys) (i : ℕ)
    (S : ∀ k, List (Γ k)) (l : List (Γ k)) :
    addU ps i (update S k l) = update (addU ps i S) k l := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [addU_of_not_mem hk]
  · simp only [addU, update_of_ne h]

theorem stepAux_pushAll {ps : List (Σ k, Γ k)} (hps : ps.NodupKeys) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushAll ps q) v S = TM2.stepAux q v (addU ps 1 S) := by
  induction ps generalizing S with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨a, x⟩ := p
      rw [List.nodupKeys_cons] at hps
      simp only [pushAll, List.foldr_cons, TM2.stepAux] at ih ⊢
      rw [ih hps.2]
      congr 1
      funext k
      by_cases h : k = a
      · subst h
        simp [addU, List.dlookup_eq_none.2 hps.1, List.dlookup_cons_eq]
      · simp only [addU, update_of_ne h, List.dlookup_cons_ne ps ⟨a, x⟩ h]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Counter transfer loop.** For a stack $k$, a list $ps$ of pairs $(t, x)$ of a stack $t$ and a
symbol $x$ of stack $t$, and labels $\ell$ and $\ell'$, this machine statement pops stack $k$,
stores in the state whether a symbol was popped, and branches on it: if a symbol was popped, it
pushes $x$ onto $t$ for each pair $(t, x)$ of $ps$ in list order and goes to $\ell$; if stack $k$
was empty, it goes to $\ell'$.

Placed at label $\ell$, it pops $k$ until $k$ is empty and pushes one copy of every target symbol
per popped symbol: with $ps$ empty it drains $k$, with one target it moves the counter, and with
two targets it copies it. -/
def xfer (k : K) (ps : List (Σ k, Γ k)) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (pushAll ps (.goto fun _ => self)) (.goto fun _ => next))

/-- **Running a counter transfer.** Let $M$ be a multi-stack machine whose state carries a
flag bit, and suppose that at label $\ell$ it executes the transfer loop that empties stack $k$
into the targets $p_1, \dots, p_m$ and then goes to label $\ell'$. Here each target $p_i$ is a
pair of a stack $t_i$ and a symbol $x_i$ of its alphabet, the stacks $t_1, \dots, t_m$ are
distinct, and $k$ is none of them. Let $u$ be a symbol of stack $k$. Then for every $n$, every
state $v$ and all stack contents $S$ in which stack $k$ holds exactly $u^n$, the machine goes in
exactly $n + 1$ steps from label $\ell$ with state $v$ and stacks $S$ to label $\ell'$ with the
state that stores the flag value false and the stacks obtained from $S$ by emptying stack $k$
and then pushing $n$ copies of $x_i$ on each stack $t_i$. -/
theorem xfer_run {self next : Λ} {k : K} {ps : List (Σ k, Γ k)}
    (hp : M self = xfer k ps self next) (hps : ps.NodupKeys) (hk : k ∉ ps.keys) (u : Γ k) :
    ∀ (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S k = cnt u n →
      Run M (n + 1) ⟨some self, v, S⟩ ⟨some next, Flag.tag false, addU ps n (update S k [])⟩ := by
  intro n
  induction n with
  | zero =>
      intro v S hS
      have hu : update S k [] = S := by rw [← cnt_zero u, ← hS, update_eq_self]
      refine Run.single ?_
      simp only [hp, xfer, TM2.stepAux, hS, cnt_zero, List.head?_nil, Option.isSome_none,
        List.tail_nil, Flag.untag_tag, Bool.cond_false, addU_zero]
  | succ n ih =>
      intro v S hS
      set S₁ := addU ps 1 (update S k (cnt u n)) with hS₁
      have h₁ : S₁ k = cnt u n := by rw [hS₁, addU_of_not_mem hk, update_self]
      have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
        simp only [TM2.step, hp, xfer, TM2.stepAux, hS, cnt_succ, List.head?_cons,
          Option.isSome_some, List.tail_cons, Flag.untag_tag, Bool.cond_true, stepAux_pushAll hps,
          hS₁]
      have key := Run.head hstep (ih (Flag.tag true) S₁ h₁)
      have : addU ps n (update S₁ k []) = addU ps (n + 1) (update S k []) := by
        rw [hS₁, ← addU_update hk, update_idem, addU_addU, add_comm]
      rw [this] at key
      exact key

end Xfer

theorem addU_single_self {k : K} (x : Γ k) (i : ℕ) (S : ∀ k, List (Γ k)) :
    addU [⟨k, x⟩] i S k = cnt x i ++ S k := by
  simp [addU, List.dlookup_cons_eq]

theorem addU_single_ne {k k' : K} (x : Γ k) (i : ℕ) (S : ∀ k, List (Γ k)) (h : k' ≠ k) :
    addU [⟨k, x⟩] i S k' = S k' := by
  simp [addU, List.dlookup_cons_ne _ ⟨k, x⟩ h]

omit [DecidableEq K] in
theorem single_nodupKeys {k : K} (x : Γ k) : List.NodupKeys [(⟨k, x⟩ : Σ k, Γ k)] := by
  simp [List.NodupKeys]

/-! ### Comparison of two counters -/

section Cmp

theorem compare_succ_succ (m n : ℕ) : compare (m + 1) (n + 1) = compare m n := by
  rcases lt_trichotomy m n with h | h | h
  · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]
  · rw [Nat.compare_eq_eq.2 h, Nat.compare_eq_eq.2 (by omega)]
  · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-- **One round of counter comparison.** For stacks $a, b, t_a, t_b$, symbols $u_{t_a}$ of stack
$t_a$ and $u_{t_b}$ of stack $t_b$, and labels $\mathit{self}$, $\mathit{lt}$, $\mathit{eq}$ and
$\mathit{gt}$, this machine statement pops stack $a$ and then stack $b$; after each pop it stores
in the state whether the pop found a symbol and branches on it. If both pops found a symbol, it
pushes $u_{t_a}$ onto $t_a$, then $u_{t_b}$ onto $t_b$, and goes to $\mathit{self}$. If only the
pop of $a$ found a symbol, it pushes $u_{t_a}$ onto $t_a$ and goes to $\mathit{gt}$; if only the
pop of $b$ found one, it pushes $u_{t_b}$ onto $t_b$ and goes to $\mathit{lt}$; if neither did,
it goes to $\mathit{eq}$. -/
def cmpStep (a b ta tb : K) (uta : Γ ta) (utb : Γ tb)
    (self lt eq gt : Λ) : TM2.Stmt Γ Λ σ :=
  .pop a (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
    (.pop b (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
      (.push ta (fun _ => uta) <| .push tb (fun _ => utb) <| .goto fun _ => self)
      (.push ta (fun _ => uta) <| .goto fun _ => gt))
    (.pop b (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
      (.push tb (fun _ => utb) <| .goto fun _ => lt)
      (.goto fun _ => eq))

/-- **The comparison loop.** Let $a, b, t_a, t_b$ be pairwise distinct stacks with unit symbols
$u_a, u_b, u_{t_a}, u_{t_b}$, and let $r$ map each ordering to a label. Suppose the machine $M$
has at label $\ell$ the comparison round of $a$ and $b$ with scratch stacks $t_a, t_b$ and units
$u_{t_a}, u_{t_b}$ that repeats at $\ell$ and exits to $r(\mathrm{lt})$, $r(\mathrm{eq})$ and
$r(\mathrm{gt})$: it pops $a$ and $b$, pushes $u_{t_a}$ onto $t_a$ if $a$ was non-empty and
$u_{t_b}$ onto $t_b$ if $b$ was non-empty, and goes to $\ell$ if both were non-empty, to
$r(\mathrm{lt})$ if only $b$ was, to $r(\mathrm{eq})$ if neither was and to $r(\mathrm{gt})$ if
only $a$ was. Then for all $m, n, p, q \in \mathbb{N}$, every state $v$ and all stacks $S$ in
which $a, b, t_a, t_b$ hold exactly $u_a^m, u_b^n, u_{t_a}^p, u_{t_b}^q$ respectively, there are
a state $v'$ and stacks $S'$ such that exactly $\min(m, n) + 1$ steps of $M$ lead from label
$\ell$ with state $v$ and stacks $S$ to label $r(\mathrm{compare}(m, n))$ with state $v'$ and
stacks $S'$, where in $S'$ the stack $a$ holds $u_a^{m - \min(m, n+1)}$, $b$ holds
$u_b^{n - \min(n, m+1)}$, $t_a$ holds $u_{t_a}^{p + \min(m, n+1)}$, $t_b$ holds
$u_{t_b}^{q + \min(n, m+1)}$, and every other stack is as in $S$. -/
theorem cmpLoop_run {a b ta tb : K} {ua : Γ a} {ub : Γ b} {uta : Γ ta} {utb : Γ tb}
    {self : Λ} {r : Ordering → Λ}
    (hp : M self = cmpStep a b ta tb uta utb self (r .lt) (r .eq) (r .gt))
    (hab : a ≠ b) (hata : a ≠ ta) (hatb : a ≠ tb) (hbta : b ≠ ta) (hbtb : b ≠ tb)
    (htt : ta ≠ tb) :
    ∀ (m n p q : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S a = cnt ua m → S b = cnt ub n →
      S ta = cnt uta p → S tb = cnt utb q →
      ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Run M (min m n + 1) ⟨some self, v, S⟩ ⟨some (r (compare m n)), v', S'⟩ ∧
        S' a = cnt ua (m - min m (n + 1)) ∧ S' b = cnt ub (n - min n (m + 1)) ∧
        S' ta = cnt uta (p + min m (n + 1)) ∧ S' tb = cnt utb (q + min n (m + 1)) ∧
        ∀ k, k ≠ a → k ≠ b → k ≠ ta → k ≠ tb → S' k = S k := by
  intro m
  induction m with
  | zero =>
      intro n p q v S ha hb hta htb
      rcases n with _ | n
      · refine ⟨Flag.tag false, S, Run.single ?_, by simpa using ha, by simpa using hb,
          by simpa using hta, by simpa using htb, fun _ _ _ _ _ => rfl⟩
        have hua : update S a [] = S := by rw [← cnt_zero ua, ← ha, update_eq_self]
        have hub : update S b [] = S := by rw [← cnt_zero ub, ← hb, update_eq_self]
        simp only [hp, cmpStep, TM2.stepAux, ha, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, Bool.cond_false, hua, hb, hub]
        rfl
      · refine ⟨Flag.tag true, update (update S b (cnt ub n)) tb (utb :: cnt utb q),
          Run.single ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Nat.compare_eq_lt.2 (by omega)]
          have hua : update S a [] = S := by rw [← cnt_zero ua, ← ha, update_eq_self]
          simp only [hp, cmpStep, TM2.stepAux, ha, cnt_zero, List.head?_nil, List.tail_nil,
            Option.isSome_none, Flag.untag_tag, Bool.cond_false, hua, hb, cnt_succ,
            List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
            update_of_ne hbtb.symm, htb]
        · simp [update_of_ne hatb, update_of_ne hab, ha]
        · simp [update_of_ne hbtb]
        · simp [update_of_ne htt, update_of_ne hbta.symm, hta]
        · simp [cnt_succ]
        · intro k h1 h2 h3 h4; simp [update_of_ne h4, update_of_ne h2]
  | succ m ih =>
      intro n p q v S ha hb hta htb
      rcases n with _ | n
      · refine ⟨Flag.tag false, update (update S a (cnt ua m)) ta (uta :: cnt uta p),
          Run.single ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Nat.compare_eq_gt.2 (by omega)]
          have hub : update (update S a (cnt ua m)) b [] = update S a (cnt ua m) := by
            rw [← cnt_zero ub, ← hb, ← update_of_ne hab.symm (cnt ua m) S, update_eq_self]
          simp only [hp, cmpStep, TM2.stepAux, ha, cnt_succ, List.head?_cons, List.tail_cons,
            Option.isSome_some, Flag.untag_tag, Bool.cond_true, update_of_ne hab.symm, hb,
            cnt_zero, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, hub,
            update_of_ne hata.symm, hta]
        · simp [update_of_ne hata]
        · simp [update_of_ne hbta, update_of_ne hab.symm, hb]
        · simp [cnt_succ]
        · simp [update_of_ne htt.symm, update_of_ne hatb.symm, htb]
        · intro k h1 h2 h3 h4; simp [update_of_ne h3, update_of_ne h1]
      · set S₁ := update (update (update (update S a (cnt ua m)) b (cnt ub n)) ta
          (uta :: cnt uta p)) tb (utb :: cnt utb q) with hS₁
        have h₁a : S₁ a = cnt ua m := by
          simp [hS₁, update_of_ne hatb, update_of_ne hata, update_of_ne hab]
        have h₁b : S₁ b = cnt ub n := by simp [hS₁, update_of_ne hbtb, update_of_ne hbta]
        have h₁ta : S₁ ta = cnt uta (p + 1) := by
          simp [hS₁, update_of_ne htt, cnt_succ]
        have h₁tb : S₁ tb = cnt utb (q + 1) := by simp [hS₁, cnt_succ]
        obtain ⟨v', S', hrun, h'a, h'b, h'ta, h'tb, h'k⟩ :=
          ih n (p + 1) (q + 1) (Flag.tag true) S₁ h₁a h₁b h₁ta h₁tb
        refine ⟨v', S', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
            simp only [TM2.step, hp, cmpStep, TM2.stepAux, ha, cnt_succ, List.head?_cons,
              List.tail_cons, Option.isSome_some, Flag.untag_tag, Bool.cond_true,
              update_of_ne hab.symm, hb, update_of_ne hbta.symm, update_of_ne hata.symm, hta,
              update_of_ne htt.symm, update_of_ne hbtb.symm, update_of_ne hatb.symm, htb, hS₁]
          have := Run.head hstep hrun
          rw [compare_succ_succ]
          exact this.of_eq (by omega)
        · rw [h'a]; congr 1; omega
        · rw [h'b]; congr 1; omega
        · rw [h'ta]; congr 1; omega
        · rw [h'tb]; congr 1; omega
        · intro k h1 h2 h3 h4
          rw [h'k k h1 h2 h3 h4]
          simp [hS₁, update_of_ne h1, update_of_ne h2, update_of_ne h3, update_of_ne h4]

/-- **Non-destructive comparison of two counters.** Let $M$ be a TM2 machine whose state type
carries a flag bit, let $a, b, t_a, t_b$ be pairwise distinct stacks with symbols $u_a$, $u_b$,
$u_{t_a}$, $u_{t_b}$ of their alphabets, let $\ell$ be a label and let $r$, $r'$, $o$ map each
ordering to a label. Suppose that $M$ has at $\ell$ the comparison round of $a$ and $b$ with
scratch stacks $t_a, t_b$ and units $u_{t_a}, u_{t_b}$ that goes to $\ell$ again and exits to
$r(\mathrm{lt})$, $r(\mathrm{eq})$ and $r(\mathrm{gt})$, and that for every ordering $\omega$,
$M$ has at $r(\omega)$ the counter transfer loop of $t_a$ into the single target $(a, u_a)$ that
repeats at $r(\omega)$ and exits to $r'(\omega)$, and has at $r'(\omega)$ the counter transfer
loop of $t_b$ into the single target $(b, u_b)$ that repeats at $r'(\omega)$ and exits to
$o(\omega)$. Write $\mathrm{compare}(m, n)$ for the ordering of natural numbers $m$ and $n$, and
$[m \ne n]$ for $1$ if $m \ne n$ and $0$ otherwise. Then for all $m, n \in \mathbb{N}$, every
state $v$ and all stacks $S$ in which $a$ holds exactly $u_a^m$, $b$ holds exactly $u_b^n$ and
$t_a$ and $t_b$ are empty, $M$ runs in exactly $3\min(m, n) + 3 + [m \ne n]$ steps from label
$\ell$ with state $v$ and stacks $S$ to label $o(\mathrm{compare}(m, n))$ with the state that
stores the flag value false and with the same stacks $S$. -/
theorem cmp_run {a b ta tb : K} {ua : Γ a} {ub : Γ b} {uta : Γ ta} {utb : Γ tb}
    {self : Λ} {r rB out : Ordering → Λ}
    (hp : M self = cmpStep a b ta tb uta utb self (r .lt) (r .eq) (r .gt))
    (hA : ∀ o, M (r o) = xfer ta [⟨a, ua⟩] (r o) (rB o))
    (hB : ∀ o, M (rB o) = xfer tb [⟨b, ub⟩] (rB o) (out o))
    (hab : a ≠ b) (hata : a ≠ ta) (hatb : a ≠ tb) (hbta : b ≠ ta) (hbtb : b ≠ tb)
    (htt : ta ≠ tb) (m n : ℕ) (v : σ) (S : ∀ k, List (Γ k)) (ha : S a = cnt ua m)
    (hb : S b = cnt ub n) (hta : S ta = []) (htb : S tb = []) :
    Run M (3 * min m n + 3 + (if m = n then 0 else 1)) ⟨some self, v, S⟩
      ⟨some (out (compare m n)), Flag.tag false, S⟩ := by
  obtain ⟨v', S', h₁, h'a, h'b, h'ta, h'tb, h'k⟩ :=
    cmpLoop_run hp hab hata hatb hbta hbtb htt m n 0 0 v S ha hb hta htb
  have h₂ := xfer_run (hA (compare m n)) (single_nodupKeys ua) (by simpa using hata.symm) uta
    (0 + min m (n + 1)) v' S' h'ta
  set S'' := addU [⟨a, ua⟩] (0 + min m (n + 1)) (update S' ta []) with hS''
  have h''tb : S'' tb = cnt utb (0 + min n (m + 1)) := by
    rw [hS'', addU_single_ne _ _ _ hatb.symm, update_of_ne htt.symm, h'tb]
  have h₃ := xfer_run (hB (compare m n)) (single_nodupKeys ub) (by simpa using hbtb.symm) utb
    (0 + min n (m + 1)) (Flag.tag false) S'' h''tb
  have hfin : addU [⟨b, ub⟩] (0 + min n (m + 1)) (update S'' tb []) = S := by
    funext k
    by_cases h1 : k = b
    · subst h1
      rw [addU_single_self, update_of_ne hbtb, hS'', addU_single_ne _ _ _ hab.symm,
        update_of_ne hbta, h'b, hb, cnt_add]
      congr 1; omega
    rw [addU_single_ne _ _ _ h1]
    by_cases h2 : k = tb
    · subst h2; rw [update_self, htb]
    rw [update_of_ne h2]
    by_cases h3 : k = a
    · subst h3
      rw [hS'', addU_single_self, update_of_ne hata, h'a, ha, cnt_add]
      congr 1; omega
    rw [hS'', addU_single_ne _ _ _ h3]
    by_cases h4 : k = ta
    · subst h4; rw [update_self, hta]
    rw [update_of_ne h4, h'k k h3 h1 h4 h2]
  rw [hfin] at h₃
  refine (h₁.trans (h₂.trans h₃)).of_eq ?_
  split_ifs with h <;> omega

end Cmp

/-! ### For-loops over a counter -/

/-- **Sum of consecutive values.** For $f : \mathbb{N} \to \mathbb{N}$ and $i, j \in \mathbb{N}$,
$\mathrm{sumFrom}(f, i, j) = f(i) + f(i+1) + \dots + f(i+j-1)$ is the sum of $f(t)$ over the
$j$ indices $t$ with $i \le t < i + j$; it is $0$ when $j = 0$. -/
def sumFrom (f : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => f i + sumFrom f (i + 1) j

theorem sumFrom_const (c i j : ℕ) : sumFrom (fun _ => c) i j = j * c := by
  induction j generalizing i with
  | zero => simp [sumFrom]
  | succ j ih => rw [sumFrom, ih, Nat.succ_mul, Nat.add_comm]

/-- **Termwise bound on a sum of consecutive values.** Let $f : \mathbb{N} \to \mathbb{N}$ and
$c, i, j \in \mathbb{N}$. If $f(t) \le c$ for every $t$ with $i \le t < i + j$, then
$\mathrm{sumFrom}(f, i, j) = f(i) + f(i+1) + \dots + f(i+j-1)$ is at most $j \cdot c$. -/
theorem sumFrom_le {f : ℕ → ℕ} {c : ℕ} :
    ∀ (i j : ℕ), (∀ t, i ≤ t → t < i + j → f t ≤ c) → sumFrom f i j ≤ j * c := by
  intro i j
  induction j generalizing i with
  | zero => intro _; simp [sumFrom]
  | succ j ih =>
      intro h
      have h1 := h i le_rfl (by omega)
      have h2 := ih (i + 1) (fun t ht1 ht2 => h t (by omega) (by omega))
      rw [sumFrom, Nat.succ_mul]; omega

section For

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Loop head of a for loop over a counter.** For stacks $c$ and $c'$, a symbol $u'$ of stack
$c'$ and labels $b$ and $r$, the loop head is the statement that pops stack $c$, replaces the
machine state by the state whose flag bit records whether a symbol was popped, and branches on
that bit: if a symbol was popped, it pushes $u'$ onto the index stack $c'$ and goes to label $b$
(the loop body); if $c$ was empty, it goes to label $r$. -/
def forHead (c cd : K) (ucd : Γ cd) (body rest : Λ) : TM2.Stmt Γ Λ σ :=
  .pop c (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
    (.push cd (fun _ => ucd) <| .goto fun _ => body) (.goto fun _ => rest)

/-- **Exact running time of a for loop over a counter.** Let $M$ be a multi-stack machine whose
states carry a flag bit, with $\mathrm{tag}(\beta)$ the state storing the bit $\beta$; write $(\ell,
v, S)$ for the configuration at label $\ell$ with state $v$ and stack contents $S$, and $u^m$ for a
stack holding exactly $m$ copies of the symbol $u$. Let $c \ne c'$ be stacks with a symbol $u$ of
stack $c$ and a symbol $u'$ of stack $c'$, and let $h, b, r, e$ be labels such that at $h$ the
machine runs the loop head on $c$ with index stack $c'$ (pop $c$; if a symbol was popped, push $u'$
onto $c'$ and go to $b$, otherwise go to $r$), and at $r$ it runs the transfer that drains $c'$,
pushing one $u$ onto $c$ per popped symbol, and then goes to $e$. Let $n \in \mathbb{N}$, let
$\mathrm{cost} : \mathbb{N} \to \mathbb{N}$, and let $P(i, S)$ be a predicate such that $P(i, S)$
implies $P(i, S')$ whenever $S$ and $S'$ agree on every stack other than $c$ and $c'$. Assume that
for every $i < n$ and all stack contents $S$ with $S_c = u^{n-1-i}$, $S_{c'} = u'^{\,i+1}$ and $P(i,
S)$, there are a state $v'$ and stack contents $S'$ such that $M$ goes from $(b,
\mathrm{tag}(\mathrm{true}), S)$ to $(h, v', S')$ in exactly $\mathrm{cost}(i)$ steps, with $S'_c =
S_c$, $S'_{c'} = S_{c'}$ and $P(i + 1, S')$. Then for every state $v$ and all stack contents $S$
with $S_c = u^n$, $S_{c'}$ empty and $P(0, S)$, there are stack contents $S'$ such that $M$ goes
from $(h, v, S)$ to $(e, \mathrm{tag}(\mathrm{false}), S')$ in exactly $\sum_{i < n}
(\mathrm{cost}(i) + 1) + n + 2$ steps, with $S'_c = u^n$, $S'_{c'}$ empty and $P(n, S')$. -/
theorem forLoop_run {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (cost : ℕ → ℕ)
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Run M (cost i) ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      Run M (sumFrom (fun i => cost i + 1) 0 n + n + 2) ⟨some head, v, S⟩
        ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by
  -- the loop proper, from iteration `i` with `j` iterations left
  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        Run M (sumFrom (fun i => cost i + 1) i j + 1) ⟨some head, v, S⟩
          ⟨some rest, Flag.tag false, S'⟩ ∧ S' c = [] ∧ S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, Run.single ?_, h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, Bool.cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, Bool.cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        refine (Run.head hstep (hrun.trans hrun')).of_eq ?_
        simp only [sumFrom]; omega
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx :=
    xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n (Flag.tag false) S' h'cd
  refine ⟨_, (hrun.trans hx).of_eq (by omega), ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end For

/-! ### Emitting constant symbols -/

section Emit

/-- **Pushing a list of symbols onto one stack.** Let $k$ be a stack index, $xs = [x_1, \dots, x_m]$
a list of symbols of the alphabet of stack $k$, and $q$ a statement of a TM2 machine. This is the
statement that pushes $x_1, \dots, x_m$ onto stack $k$ in that order, so that $x_m$ ends on top
when $m \ge 1$, and then continues with $q$. -/
def pushList (k : K) (xs : List (Γ k)) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  xs.foldr (fun x q => .push k (fun _ => x) q) q

theorem stepAux_pushList (k : K) (xs : List (Γ k)) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushList k xs q) v S = TM2.stepAux q v (update S k (xs.reverse ++ S k)) := by
  induction xs generalizing S with
  | nil => simp [pushList]
  | cons x xs ih =>
      simp only [pushList, List.foldr_cons, TM2.stepAux] at ih ⊢
      rw [ih, update_self, update_idem]
      simp

variable {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Pushing a constant list.** For a stack $k$, a list $(x_1, \dots, x_m)$ of symbols of
stack $k$ and a label $\ell$, this statement pushes $x_1, \dots, x_m$ onto stack $k$ in this order,
so that $x_m$ ends on top, and then goes to label $\ell$. The machine executes it in a single
step. -/
def emit (k : K) (xs : List (Γ k)) (next : Λ) : TM2.Stmt Γ Λ σ :=
  pushList k xs (.goto fun _ => next)

theorem emit_run {self next : Λ} {k : K} {xs : List (Γ k)} (hp : M self = emit k xs next)
    (v : σ) (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (xs.reverse ++ S k)⟩ :=
  Run.single (by rw [hp, emit, stepAux_pushList]; rfl)

end Emit

/-! ### Counter arithmetic -/

section Arith

omit [DecidableEq K] in
theorem pair_nodupKeys {a b : K} (x : Γ a) (y : Γ b) (h : a ≠ b) :
    List.NodupKeys [(⟨a, x⟩ : Σ k, Γ k), ⟨b, y⟩] := by
  simp [List.NodupKeys, h]

theorem addU_pair_fst {a b : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k)) :
    addU [⟨a, x⟩, ⟨b, y⟩] i S a = cnt x i ++ S a := by
  simp [addU, List.dlookup_cons_eq]

theorem addU_pair_snd {a b : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k)) (h : b ≠ a) :
    addU [⟨a, x⟩, ⟨b, y⟩] i S b = cnt y i ++ S b := by
  simp [addU, List.dlookup_cons_ne _ ⟨a, x⟩ h, List.dlookup_cons_eq]

theorem addU_pair_ne {a b k : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k))
    (ha : k ≠ a) (hb : k ≠ b) : addU [⟨a, x⟩, ⟨b, y⟩] i S k = S k := by
  simp [addU, List.dlookup_cons_ne _ ⟨a, x⟩ ha, List.dlookup_cons_ne _ ⟨b, y⟩ hb]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Copying a counter through a scratch stack.** Let $a, c, t$ be pairwise distinct stacks with
unit symbols $u_a, u_c, u_t$. Write $\mathrm{xfer}(k, ps, \ell, \ell')$ for the transfer loop at
label $\ell$ that pops stack $k$ until it is empty, pushing $x$ onto stack $j$ for each pair
$(j, x)$ in $ps$ per popped symbol, and then goes to $\ell'$. Suppose the machine $M$ has
$M(l_1) = \mathrm{xfer}(a, [(c, u_c), (t, u_t)], l_1, l_2)$ and
$M(l_2) = \mathrm{xfer}(t, [(a, u_a)], l_2, \mathit{next})$. Let $m, p \in \mathbb{N}$, let $v$
be a state and let $S$ be stacks in which $a$ holds exactly $u_a^m$, $c$ holds $u_c^p$ and $t$ is
empty. Then exactly $2m + 2$ steps of $M$ lead from label $l_1$ with state $v$ and stacks $S$ to
label $\mathit{next}$ with the state storing the flag false and the stacks $S$ with $c$ replaced
by $u_c^{m+p}$. -/
theorem copy_run {a c t : K} {ua : Γ a} {uc : Γ c} {ut : Γ t} {l₁ l₂ next : Λ}
    (h₁ : M l₁ = xfer a [⟨c, uc⟩, ⟨t, ut⟩] l₁ l₂) (h₂ : M l₂ = xfer t [⟨a, ua⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (m p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (ha : S a = cnt ua m) (hc : S c = cnt uc p) (ht : S t = []) :
    Run M (2 * m + 2) ⟨some l₁, v, S⟩ ⟨some next, Flag.tag false, update S c (cnt uc (m + p))⟩ := by
  have r₁ := xfer_run h₁ (pair_nodupKeys uc ut hct) (by simp [hac, hat]) ua m v S ha
  set S₁ := addU [⟨c, uc⟩, ⟨t, ut⟩] m (update S a []) with hS₁
  have h₁t : S₁ t = cnt ut m := by
    rw [hS₁, addU_pair_snd _ _ _ _ hct.symm, update_of_ne hat.symm, ht, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys ua) (by simp [hat.symm]) ut m (Flag.tag false) S₁ h₁t
  have hfin : addU [⟨a, ua⟩] m (update S₁ t []) = update S c (cnt uc (m + p)) := by
    funext k
    by_cases hka : k = a
    · subst hka
      rw [addU_single_self, update_of_ne hat, hS₁, addU_pair_ne _ _ _ _ hac hat, update_self,
        update_of_ne hac, ha, List.append_nil]
    rw [addU_single_ne _ _ _ hka]
    by_cases hkt : k = t
    · subst hkt; rw [update_self, update_of_ne hct.symm, ht]
    rw [update_of_ne hkt]
    by_cases hkc : k = c
    · subst hkc
      rw [hS₁, addU_pair_fst, update_of_ne (Ne.symm hac), hc, cnt_add, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkt, update_of_ne hka, update_of_ne hkc]
  rw [hfin] at r₂
  exact (r₁.trans r₂).of_eq (by omega)

/-- **Adding two counters into a third.** Let $a, b, c, t$ be stacks with $a \ne c$, $a \ne t$,
$b \ne c$, $b \ne t$ and $c \ne t$, with unit symbols $u_a, u_b, u_c, u_t$. Write
$\mathrm{xfer}(k, ps, \ell, \ell')$ for the transfer loop at label $\ell$ that pops stack $k$ until
it is empty, pushing $x$ onto stack $j$ for each pair $(j, x)$ in $ps$ per popped symbol, and then
goes to $\ell'$. Suppose the machine $M$ has
$M(l_1) = \mathrm{xfer}(a, [(c, u_c), (t, u_t)], l_1, l_2)$,
$M(l_2) = \mathrm{xfer}(t, [(a, u_a)], l_2, l_3)$,
$M(l_3) = \mathrm{xfer}(b, [(c, u_c), (t, u_t)], l_3, l_4)$ and
$M(l_4) = \mathrm{xfer}(t, [(b, u_b)], l_4, \mathit{next})$. Let $m, n, p \in \mathbb{N}$, let $v$
be a state and let $S$ be stacks in which $a$ holds exactly $u_a^m$, $b$ holds $u_b^n$, $c$ holds
$u_c^p$ and $t$ is empty. Then exactly $2m + 2n + 4$ steps of $M$ lead from label $l_1$ with
state $v$ and stacks $S$ to label $\mathit{next}$ with the state storing the flag false and the
stacks $S$ with $c$ replaced by $u_c^{m+n+p}$. -/
theorem add_run {a b c t : K} {ua : Γ a} {ub : Γ b} {uc : Γ c} {ut : Γ t}
    {l₁ l₂ l₃ l₄ next : Λ}
    (h₁ : M l₁ = xfer a [⟨c, uc⟩, ⟨t, ut⟩] l₁ l₂) (h₂ : M l₂ = xfer t [⟨a, ua⟩] l₂ l₃)
    (h₃ : M l₃ = xfer b [⟨c, uc⟩, ⟨t, ut⟩] l₃ l₄) (h₄ : M l₄ = xfer t [⟨b, ub⟩] l₄ next)
    (hac : a ≠ c) (hat : a ≠ t) (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t) (m n p : ℕ) (v : σ)
    (S : ∀ k, List (Γ k)) (ha : S a = cnt ua m) (hb : S b = cnt ub n) (hc : S c = cnt uc p)
    (ht : S t = []) :
    Run M (2 * m + 2 * n + 4) ⟨some l₁, v, S⟩
      ⟨some next, Flag.tag false, update S c (cnt uc (m + n + p))⟩ := by
  have r₁ := copy_run h₁ h₂ hac hat hct m p v S ha hc ht
  have r₂ := copy_run h₃ h₄ hbc hbt hct n (m + p) (Flag.tag false) (update S c (cnt uc (m + p)))
    (by rw [update_of_ne hbc, hb]) (by rw [update_self]) (by rw [update_of_ne hct.symm, ht])
  rw [update_idem, show n + (m + p) = m + n + p by omega] at r₂
  exact (r₁.trans r₂).of_eq (by omega)

/-- **Multiplying unary counters.** Let $M$ be a multi-stack machine whose states carry a flag
bit, with $\mathrm{tag}(\mathrm{false})$ the state storing the bit false; write $(\ell, v, S)$ for
the configuration at label $\ell$ with state $v$ and stack contents $S$, and $u^m$ for a stack
holding exactly $m$ copies of the symbol $u$. Let $a, a', b, c, t$ be pairwise distinct stacks
with symbols $u_a, u_{a'}, u_b, u_c, u_t$ of the respective stacks, and let $h, \ell_1, \ell_2, r,
e$ be labels such that: at $h$ the machine runs the loop head on $a$ with index stack $a'$ (pop
$a$; if a symbol was popped, push $u_{a'}$ onto $a'$ and go to $\ell_1$, otherwise go to $r$); at
$\ell_1$ it runs the transfer that drains $b$, pushing $u_c$ onto $c$ and $u_t$ onto $t$ per
popped symbol, and then goes to $\ell_2$; at $\ell_2$ it runs the transfer that drains $t$,
pushing $u_b$ onto $b$ per popped symbol, and then goes to $h$; and at $r$ it runs the transfer
that drains $a'$, pushing $u_a$ onto $a$ per popped symbol, and then goes to $e$. Then for all
$m, n, p \in \mathbb{N}$, every state $v$ and all stack contents $S$ with $S_a = u_a^m$, $S_{a'}$
empty, $S_b = u_b^n$, $S_c = u_c^p$ and $S_t$ empty, $M$ goes from $(h, v, S)$ to
$(e, \mathrm{tag}(\mathrm{false}), S')$ in exactly $m(2n + 3) + m + 2$ steps, where $S'$ agrees
with $S$ on every stack except $c$ and $S'_c = u_c^{mn + p}$. -/
theorem mul_run {a ad b c t : K} {ua : Γ a} {uad : Γ ad} {ub : Γ b} {uc : Γ c} {ut : Γ t}
    {head body l₂ rest next : Λ}
    (hHead : M head = forHead a ad uad body rest)
    (hBody : M body = xfer b [⟨c, uc⟩, ⟨t, ut⟩] body l₂)
    (hL₂ : M l₂ = xfer t [⟨b, ub⟩] l₂ head)
    (hRest : M rest = xfer ad [⟨a, ua⟩] rest next)
    (hnd : [a, ad, b, c, t].Nodup) (m n p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (ha : S a = cnt ua m) (had : S ad = []) (hb : S b = cnt ub n) (hc : S c = cnt uc p)
    (ht : S t = []) :
    Run M (m * (2 * n + 3) + m + 2) ⟨some head, v, S⟩
      ⟨some next, Flag.tag false, update S c (cnt uc (m * n + p))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haad, hab, hac, hat⟩, ⟨hadb, hadc, hadt⟩, ⟨hbc, hbt⟩, hct, -⟩ := hnd
  let P : ℕ → (∀ k, List (Γ k)) → Prop := fun i S' =>
    ∀ k, k ≠ a → k ≠ ad → S' k = update S c (cnt uc (i * n + p)) k
  have h0 : P 0 S := fun k _ _ => by
    by_cases hkc : k = c
    · subst hkc; rw [update_self, hc]; simp
    · rw [update_of_ne hkc]
  obtain ⟨S', hrun, h'a, h'ad, h'P⟩ := forLoop_run (c := a) (cd := ad) (uc := ua) (ucd := uad)
    hHead hRest haad m P (fun i S₁ S₂ h hP k h1 h2 => by rw [h k h1 h2, hP k h1 h2])
    (fun _ => 2 * n + 2)
    (fun i _ S₁ h₁a h₁ad hP => by
      have hb₁ : S₁ b = cnt ub n := by
        rw [hP b (Ne.symm hab) (Ne.symm hadb), update_of_ne hbc, hb]
      have hc₁ : S₁ c = cnt uc (i * n + p) := by
        rw [hP c (Ne.symm hac) (Ne.symm hadc), update_self]
      have ht₁ : S₁ t = [] := by
        rw [hP t (Ne.symm hat) (Ne.symm hadt), update_of_ne (Ne.symm hct), ht]
      refine ⟨_, _, copy_run hBody hL₂ hbc hbt hct n (i * n + p) (Flag.tag true) S₁ hb₁ hc₁ ht₁,
        by rw [update_of_ne hac], by rw [update_of_ne hadc], fun k h1 h2 => ?_⟩
      by_cases hkc : k = c
      · subst hkc
        rw [update_self, update_self]
        congr 1; rw [Nat.succ_mul]; omega
      · rw [update_of_ne hkc, hP k h1 h2, update_of_ne hkc, update_of_ne hkc])
    v S ha had h0
  have hS' : S' = update S c (cnt uc (m * n + p)) := by
    funext k
    by_cases hka : k = a
    · subst hka; rw [h'a, update_of_ne hac, ha]
    by_cases hkad : k = ad
    · subst hkad; rw [h'ad, update_of_ne hadc, had]
    exact h'P k hka hkad
  rw [hS', sumFrom_const] at hrun
  exact hrun

end Arith

/-! ### Prepending emission: repeated blocks and gaps -/

section Gap

/-- **Repeated block.** For a list $ys$ and $n \in \mathbb{N}$, $\mathrm{rep}(ys, n)$ is the
concatenation of $n$ copies of $ys$; it is the empty list when $n = 0$. -/
def rep {α : Type} (ys : List α) (n : ℕ) : List α := (List.replicate n ys).flatten

@[simp] theorem rep_zero {α : Type} (ys : List α) : rep ys 0 = [] := rfl

theorem rep_succ {α : Type} (ys : List α) (n : ℕ) : rep ys (n + 1) = ys ++ rep ys n := by
  simp [rep, List.replicate_succ]

theorem rep_succ' {α : Type} (ys : List α) (n : ℕ) : rep ys (n + 1) = rep ys n ++ ys := by
  simp [rep, List.replicate_succ']

theorem rep_add {α : Type} (ys : List α) (m n : ℕ) : rep ys (m + n) = rep ys m ++ rep ys n := by
  unfold rep; rw [List.replicate_add, List.flatten_append]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Prepending a constant list.** For a stack $k$, a list $(y_1, \dots, y_m)$ of symbols of
stack $k$ and a label $\ell$, this statement pushes $y_m, \dots, y_1$ onto stack $k$ in this order
and then goes to label $\ell$; it is the constant-list push of the reversed list. Afterwards
$y_1, \dots, y_m$ sit on top of stack $k$, read from the top down. -/
def emitR (k : K) (ys : List (Γ k)) (next : Λ) : TM2.Stmt Γ Λ σ := emit k ys.reverse next

omit [Flag σ] in
theorem emitR_run {self next : Λ} {k : K} {ys : List (Γ k)} (hp : M self = emitR k ys next)
    (v : σ) (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (ys ++ S k)⟩ := by
  simpa using emit_run (M := M) hp v S

/-- **Draining a counter while prepending a block.** Let $k$ and $o$ be stack indices, $ys$ a list
of symbols of the alphabet of stack $o$, and $\ell$ and $\ell'$ labels. This is the TM2 statement
that pops stack $k$ and sets the internal state to the flag bit recording whether a symbol was
popped. If one was, it prepends $ys$ to stack $o$ (so that $ys$ reads from the top down) and goes
to $\ell$; if stack $k$ was empty, it goes to $\ell'$.

Used as the statement at label $\ell$ with $k \ne o$, it empties a unary counter on stack $k$ and
prepends one copy of $ys$ to stack $o$ per unit removed, then goes to $\ell'$. -/
def xferE (k o : K) (ys : List (Γ o)) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (pushList o ys.reverse (.goto fun _ => self)) (.goto fun _ => next))

theorem xferE_run {self next : Λ} {k o : K} {ys : List (Γ o)}
    (hp : M self = xferE k o ys self next) (hko : k ≠ o) (u : Γ k) :
    ∀ (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S k = cnt u n →
      Run M (n + 1) ⟨some self, v, S⟩
        ⟨some next, Flag.tag false, update (update S k []) o (rep ys n ++ S o)⟩ := by
  intro n
  induction n with
  | zero =>
      intro v S hS
      refine Run.single ?_
      have hu : update S k [] = S := by rw [← cnt_zero u, ← hS, update_eq_self]
      simp only [hp, xferE, TM2.stepAux, hS, cnt_zero, List.head?_nil, Option.isSome_none,
        List.tail_nil, Flag.untag_tag, Bool.cond_false, hu, rep_zero, List.nil_append,
        update_eq_self]
  | succ n ih =>
      intro v S hS
      set S₁ := update (update S k (cnt u n)) o (ys ++ S o) with hS₁
      have h₁ : S₁ k = cnt u n := by rw [hS₁, update_of_ne hko, update_self]
      have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
        simp only [TM2.step, hp, xferE, TM2.stepAux, hS, cnt_succ, List.head?_cons,
          Option.isSome_some, List.tail_cons, Flag.untag_tag, Bool.cond_true, stepAux_pushList,
          List.reverse_reverse, update_of_ne (Ne.symm hko), hS₁]
      have key := Run.head hstep (ih (Flag.tag true) S₁ h₁)
      have hfin : update (update S₁ k []) o (rep ys n ++ S₁ o) =
          update (update S k []) o (rep ys (n + 1) ++ S o) := by
        funext j
        by_cases hjo : j = o
        · subst hjo; rw [update_self, update_self, hS₁, update_self, rep_succ', List.append_assoc]
        rw [update_of_ne hjo, update_of_ne hjo]
        by_cases hjk : j = k
        · subst hjk; rw [update_self, update_self]
        rw [update_of_ne hjk, update_of_ne hjk, hS₁, update_of_ne hjo, update_of_ne hjk]
      rw [hfin] at key
      exact key

/-- **Gap emission.** Let $P, Q, T_1, T_2, o$ be pairwise distinct stacks, with unit symbols
$u_P, u_Q, u_{T_1}, u_{T_2}$ for the first four, and let $ys$ be a list of symbols of stack $o$.
Write $\mathrm{xfer}(k, ps, \ell, \ell')$ for the transfer loop at label $\ell$ that pops stack
$k$ until it is empty, pushing $x$ onto stack $j$ for each pair $(j, x)$ in $ps$ per popped
symbol, and then goes to $\ell'$. Let $r, r_B, \mathit{out}$ map each ordering to a label, with
$\mathit{out}(\mathrm{eq}) = \mathit{next}$ and $\mathit{out}(\omega) = \mathit{emit}$ for every
ordering $\omega \ne \mathrm{eq}$. Suppose the machine $M$ has: at label $\mathit{dec}$ the
decrement of $P$ that goes to $\mathit{cmp}$ if a symbol was popped and to $\mathit{ifZero}$ if
$P$ was empty; at label $\mathit{cmp}$ the comparison round of $P$ and $Q$ with scratch stacks
$T_1, T_2$ and units $u_{T_1}, u_{T_2}$ that repeats at $\mathit{cmp}$ and exits to
$r(\mathrm{lt})$, $r(\mathrm{eq})$ and $r(\mathrm{gt})$; for every ordering $\omega$,
$M(r(\omega)) = \mathrm{xfer}(T_1, [(P, u_P)], r(\omega), r_B(\omega))$ and
$M(r_B(\omega)) = \mathrm{xfer}(T_2, [(Q, u_Q)], r_B(\omega), \mathit{out}(\omega))$; and at
label $\mathit{emit}$ the statement that prepends $ys$ to stack $o$ (so that $ys$ reads top-down)
and goes to $\mathit{dec}$. Let $q \in \mathbb{N}$. Then for every $g \in \mathbb{N}$, every
state $v$ and all stacks $S$ in which $P$ holds exactly $u_P^{q+g+1}$, $Q$ holds $u_Q^q$, and
$T_1$ and $T_2$ are empty, exactly $g(3q + 6) + 3q + 4$ steps of $M$ lead from label
$\mathit{dec}$ with state $v$ and stacks $S$ to label $\mathit{next}$ with the state storing the
flag false and the stacks $S$ with $P$ replaced by $u_P^q$ and $o$ replaced by $g$ copies of $ys$
concatenated, followed by the old contents of $o$. -/
theorem emitDiff_run {P Q T1 T2 o : K} {uP : Γ P} {uQ : Γ Q} {uT1 : Γ T1} {uT2 : Γ T2}
    {ys : List (Γ o)} {dec cmpL emitL ifZero next : Λ} {r rB out : Ordering → Λ}
    (hdec : M dec = decr P ifZero cmpL)
    (hcmp : M cmpL = cmpStep P Q T1 T2 uT1 uT2 cmpL (r .lt) (r .eq) (r .gt))
    (hr : ∀ o, M (r o) = xfer T1 [⟨P, uP⟩] (r o) (rB o))
    (hrB : ∀ o, M (rB o) = xfer T2 [⟨Q, uQ⟩] (rB o) (out o))
    (hout : ∀ o, out o = if o = .eq then next else emitL)
    (hemit : M emitL = emitR o ys dec)
    (hnd : [P, Q, T1, T2, o].Nodup) (q : ℕ) :
    ∀ (gap : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S P = cnt uP (q + gap + 1) → S Q = cnt uQ q →
      S T1 = [] → S T2 = [] →
      Run M (gap * (3 * q + 6) + 3 * q + 4) ⟨some dec, v, S⟩
        ⟨some next, Flag.tag false, update (update S P (cnt uP q)) o (rep ys gap ++ S o)⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hPQ, hP1, hP2, hPo⟩, ⟨hQ1, hQ2, hQo⟩, ⟨h12, h1o⟩, h2o, -⟩ := hnd
  intro gap
  induction gap with
  | zero =>
      intro v S hP hQ h1 h2
      have r₁ := decr_run_cnt hdec v hP
      have r₂ := cmp_run hcmp hr hrB hPQ hP1 hP2 hQ1 hQ2 h12 q q (Flag.tag true)
        (update S P (cnt uP q)) (by rw [update_self]) (by rw [update_of_ne (Ne.symm hPQ), hQ])
        (by rw [update_of_ne (Ne.symm hP1), h1]) (by rw [update_of_ne (Ne.symm hP2), h2])
      rw [hout (compare q q), Nat.compare_eq_eq.2 rfl,
        ite_eq_left (rfl : Ordering.eq = Ordering.eq)] at r₂
      have := (r₁.trans r₂).of_eq (show _ = 0 * (3 * q + 6) + 3 * q + 4 by
        simp only [min_self, ite_eq_left]; omega)
      have e : update (update S P (cnt uP q)) o (S o) = update S P (cnt uP q) := by
        rw [← update_of_ne (Ne.symm hPo) (cnt uP q) S, update_eq_self]
      rw [rep_zero, List.nil_append, e]
      exact this
  | succ gap ih =>
      intro v S hP hQ h1 h2
      have r₁ := decr_run_cnt hdec v (show S P = cnt uP (q + gap + 1 + 1) by rw [hP]; rfl)
      have r₂ := cmp_run hcmp hr hrB hPQ hP1 hP2 hQ1 hQ2 h12 (q + gap + 1) q (Flag.tag true)
        (update S P (cnt uP (q + gap + 1))) (by rw [update_self])
        (by rw [update_of_ne (Ne.symm hPQ), hQ])
        (by rw [update_of_ne (Ne.symm hP1), h1]) (by rw [update_of_ne (Ne.symm hP2), h2])
      rw [hout (compare (q + gap + 1) q), Nat.compare_eq_gt.2 (by omega),
        ite_eq_right (show Ordering.gt ≠ Ordering.eq by decide)] at r₂
      have r₃ := emitR_run hemit (Flag.tag false) (update S P (cnt uP (q + gap + 1)))
      set S₂ := update (update S P (cnt uP (q + gap + 1))) o
        (ys ++ update S P (cnt uP (q + gap + 1)) o) with hS₂
      have r₄ := ih (Flag.tag false) S₂ (by rw [hS₂, update_of_ne hPo, update_self])
        (by rw [hS₂, update_of_ne hQo, update_of_ne (Ne.symm hPQ), hQ])
        (by rw [hS₂, update_of_ne h1o, update_of_ne (Ne.symm hP1), h1])
        (by rw [hS₂, update_of_ne h2o, update_of_ne (Ne.symm hP2), h2])
      have hfin : update (update S₂ P (cnt uP q)) o (rep ys gap ++ S₂ o) =
          update (update S P (cnt uP q)) o (rep ys (gap + 1) ++ S o) := by
        funext j
        by_cases hjo : j = o
        · subst hjo
          rw [update_self, update_self, hS₂, update_self, update_of_ne (Ne.symm hPo), rep_succ',
            List.append_assoc]
        rw [update_of_ne hjo, update_of_ne hjo]
        by_cases hjP : j = P
        · subst hjP; rw [update_self, update_self]
        rw [update_of_ne hjP, update_of_ne hjP, hS₂, update_of_ne hjo, update_of_ne hjP]
      rw [hfin] at r₄
      refine (r₁.trans (r₂.trans (r₃.trans r₄))).of_eq ?_
      have : min (q + gap + 1) q = q := by omega
      rw [this, ite_eq_right (show ¬(q + gap + 1 = q) by omega)]
      have := Nat.add_one_mul gap (3 * q + 6)
      omega

end Gap

/-! ### Runs of unspecified length, and for-loops with data-dependent bodies -/

section Reach

variable {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Reachability for a TM2 machine.** For a TM2 machine $M$ and configurations $c$ and $d$, $d$
is reachable from $c$ when there is some $n \in \mathbb{N}$ such that $M$ runs from $c$ to $d$
in exactly $n$ steps. -/
def Reach (M : Λ → TM2.Stmt Γ Λ σ) (c d : TM2.Cfg Γ Λ σ) : Prop := ∃ n, Run M n c d

theorem Run.reach {n : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) : Reach M c d := ⟨n, h⟩

theorem Reach.refl (c : TM2.Cfg Γ Λ σ) : Reach M c c := ⟨0, Run.zero c⟩

theorem Reach.of_eq {c d : TM2.Cfg Γ Λ σ} (h : c = d) : Reach M c d := h ▸ Reach.refl c

theorem Reach.trans {c d e : TM2.Cfg Γ Λ σ} (h₁ : Reach M c d) (h₂ : Reach M d e) :
    Reach M c e := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨m, h₂⟩ := h₂; exact ⟨n + m, h₁.trans h₂⟩

variable [Flag σ]

/-- **A for loop over a counter reaches its exit.** Let $M$ be a multi-stack machine whose states
carry a flag bit, with $\mathrm{tag}(\beta)$ the state storing the bit $\beta$; write $(\ell, v, S)$
for the configuration at label $\ell$ with state $v$ and stack contents $S$, and $u^m$ for a stack
holding exactly $m$ copies of the symbol $u$. Let $c \ne c'$ be stacks with a symbol $u$ of stack
$c$ and a symbol $u'$ of stack $c'$, and let $h, b, r, e$ be labels such that at $h$ the machine
runs the loop head on $c$ with index stack $c'$ (pop $c$; if a symbol was popped, push $u'$ onto
$c'$ and go to $b$, otherwise go to $r$), and at $r$ it runs the transfer that drains $c'$, pushing
one $u$ onto $c$ per popped symbol, and then goes to $e$. Let $n \in \mathbb{N}$, and let $P(i, S)$
be a predicate such that $P(i, S)$ implies $P(i, S')$ whenever $S$ and $S'$ agree on every stack
other than $c$ and $c'$. Assume that for every $i < n$ and all stack contents $S$ with $S_c =
u^{n-1-i}$, $S_{c'} = u'^{\,i+1}$ and $P(i, S)$, there are a state $v'$ and stack contents $S'$ such
that $M$ goes from $(b, \mathrm{tag}(\mathrm{true}), S)$ to $(h, v', S')$ in finitely many steps,
with $S'_c = S_c$, $S'_{c'} = S_{c'}$ and $P(i + 1, S')$. Then for every state $v$ and all stack
contents $S$ with $S_c = u^n$, $S_{c'}$ empty and $P(0, S)$, there are stack contents $S'$ such that
$M$ goes from $(h, v, S)$ to $(e, \mathrm{tag}(\mathrm{false}), S')$ in finitely many steps, with
$S'_c = u^n$, $S'_{c'}$ empty and $P(n, S')$. -/
theorem forLoop_reach {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Reach M ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      Reach M ⟨some head, v, S⟩ ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by
  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        Reach M ⟨some head, v, S⟩ ⟨some rest, Flag.tag false, S'⟩ ∧ S' c = [] ∧
          S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, (Run.single ?_).reach, h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, Bool.cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, Bool.cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        exact (Run.head hstep (Run.zero _)).reach.trans (hrun.trans hrun')
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx := xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n
    (Flag.tag false) S' h'cd
  refine ⟨_, hrun.trans hx.reach, ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end Reach

/-! ### Runs with an upper bound on their length (time bounds) -/

section Bound

variable {M : Λ → TM2.Stmt Γ Λ σ}

/-- **Runs within a step budget.** For a TM2 machine $M$, a bound $B \in \mathbb{N}$ and
configurations $c$ and $d$, $M$ runs from $c$ to $d$ within $B$ steps when there is some
$n \le B$ such that $M$ runs from $c$ to $d$ in exactly $n$ steps. -/
def RunLe (M : Λ → TM2.Stmt Γ Λ σ) (B : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  ∃ n, n ≤ B ∧ Run M n c d

/-- **Budgeted run.** For a machine $M$, numbers $K, X \in \mathbb{N}$ and configurations $c$ and
$d$, the budgeted run from $c$ to $d$ with $K$ steps already spent and budget $X$ holds when there
is an $n \in \mathbb{N}$ with $K + n \le X$ such that $n$ steps of $M$ lead from $c$ to $d$.

It is used for goal-directed chaining of runs: the chaining lemmas only increase $K$. -/
def Bud (M : Λ → TM2.Stmt Γ Λ σ) (K X : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  ∃ n, K + n ≤ X ∧ Run M n c d

theorem Run.le {n B : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) (hn : n ≤ B) :
    RunLe M B c d := ⟨n, hn, h⟩

theorem RunLe.reach {B : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : RunLe M B c d) : Reach M c d :=
  let ⟨n, _, h⟩ := h; ⟨n, h⟩

theorem RunLe.mono {B B' : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : RunLe M B c d) (hB : B ≤ B') :
    RunLe M B' c d :=
  let ⟨n, hn, h⟩ := h; ⟨n, hn.trans hB, h⟩

theorem RunLe.refl (B : ℕ) (c : TM2.Cfg Γ Λ σ) : RunLe M B c c := ⟨0, Nat.zero_le _, Run.zero c⟩

theorem RunLe.trans {a b : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : RunLe M a c d)
    (h₂ : RunLe M b d e) : RunLe M (a + b) c e := by
  obtain ⟨n, hn, h₁⟩ := h₁; obtain ⟨m, hm, h₂⟩ := h₂; exact ⟨n + m, by omega, h₁.trans h₂⟩

theorem Bud.start {X : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Bud M 0 X c d) : RunLe M X c d := by
  obtain ⟨n, hn, h⟩ := h; exact ⟨n, by omega, h⟩

theorem Run.bud {a K X : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : Run M a c d)
    (h₂ : Bud M (K + a) X d e) : Bud M K X c e := by
  obtain ⟨n, hn, h₂⟩ := h₂; exact ⟨a + n, by omega, h₁.trans h₂⟩

theorem RunLe.bud {a K X : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : RunLe M a c d)
    (h₂ : Bud M (K + a) X d e) : Bud M K X c e := by
  obtain ⟨m, hm, h₁⟩ := h₁; obtain ⟨n, hn, h₂⟩ := h₂; exact ⟨m + n, by omega, h₁.trans h₂⟩

theorem Bud.fin {K X : ℕ} {c d : TM2.Cfg Γ Λ σ} (hK : K ≤ X) (h : c = d) : Bud M K X c d :=
  h ▸ ⟨0, by omega, Run.zero c⟩

variable [Flag σ]

/-- **Time bound for a for loop over a counter.** Let $M$ be a multi-stack machine whose states
carry a flag bit, with $\mathrm{tag}(\beta)$ the state storing the bit $\beta$; write $(\ell, v, S)$
for the configuration at label $\ell$ with state $v$ and stack contents $S$, and $u^m$ for a stack
holding exactly $m$ copies of the symbol $u$. Let $c \ne c'$ be stacks with a symbol $u$ of stack
$c$ and a symbol $u'$ of stack $c'$, and let $h, b, r, e$ be labels such that at $h$ the machine
runs the loop head on $c$ with index stack $c'$ (pop $c$; if a symbol was popped, push $u'$ onto
$c'$ and go to $b$, otherwise go to $r$), and at $r$ it runs the transfer that drains $c'$, pushing
one $u$ onto $c$ per popped symbol, and then goes to $e$. Let $n \in \mathbb{N}$, let $B \in
\mathbb{N}$, and let $P(i, S)$ be a predicate such that $P(i, S)$ implies $P(i, S')$ whenever $S$
and $S'$ agree on every stack other than $c$ and $c'$. Assume that for every $i < n$ and all stack
contents $S$ with $S_c = u^{n-1-i}$, $S_{c'} = u'^{\,i+1}$ and $P(i, S)$, there are a state $v'$ and
stack contents $S'$ such that $M$ goes from $(b, \mathrm{tag}(\mathrm{true}), S)$ to $(h, v', S')$
in at most $B$ steps, with $S'_c = S_c$, $S'_{c'} = S_{c'}$ and $P(i + 1, S')$. Then for every state
$v$ and all stack contents $S$ with $S_c = u^n$, $S_{c'}$ empty and $P(0, S)$, there are stack
contents $S'$ such that $M$ goes from $(h, v, S)$ to $(e, \mathrm{tag}(\mathrm{false}), S')$ in at
most $n(B + 1) + n + 2$ steps, with $S'_c = u^n$, $S'_{c'}$ empty and $P(n, S')$. -/
theorem forLoop_le {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n B : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        RunLe M B ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      RunLe M (n * (B + 1) + n + 2) ⟨some head, v, S⟩ ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by
  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        RunLe M (j * (B + 1) + 1) ⟨some head, v, S⟩ ⟨some rest, Flag.tag false, S'⟩ ∧
          S' c = [] ∧ S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, (Run.single ?_).le (by omega), h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, Bool.cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, Bool.cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        refine (((Run.head hstep (Run.zero _)).le le_rfl).trans (hrun.trans hrun')).mono ?_
        rw [Nat.succ_mul]; omega
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx := xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n
    (Flag.tag false) S' h'cd
  refine ⟨_, (hrun.trans (hx.le le_rfl)).mono (by omega), ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end Bound

end MetaMathlibExt.TM2Program
