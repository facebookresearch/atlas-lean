/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Sit.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Sit.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, five one-line proof repairs for the pinned Mathlib; module docstring rewritten for
this repository (the source's notes and status lines dropped), missing docstrings added, long lines
wrapped.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Shift

/-!
# Cook-Levin: situation tables of a `FinTM2` and the correctness of the formula

For an arbitrary `M : FinTM2` (work alphabets may be infinite and need no `DecidableEq`), an
encoding record `Enc M` fixes finite effective alphabets and numberings of stacks and of
(label, state) pairs; `Enc.ofFinTM2` builds one classically for every `M`. From it this file
defines the finite tables `la, wa, na, sa, pl, cn, pu` that the clause generators take as
parameters: a *situation* is a (label, state) pair together with the window of top cells it reads.

The step on a situation is defined on `Option Λ`; the halted label `none` steps to itself with no
pushes and no consumption, so halted rows need no separate family.

Main results:
* `eff_agree`, `step_agree`, `Enc.table_agree`, `Enc.table_agree_run`: the tables agree with
  `TM2.step`;
* `Enc.decRow` and its round trips: decoding a row of the tableau;
* `sh_force`, `Enc.sh_step_run`: the shift clauses force the next row's cells;
* `Enc.accept_sound`, `Enc.accept_complete`, and `Enc.five_iff`: the conjunction of the five
  families is satisfiable iff some certificate makes `M` accept within `T` steps;
* `runI_haltList`: the link to `TM2OutputsInTime`.

Concrete checks of the tables against real runs of two small machines are in
`CSLibExtTest/Computability/Complexity/CookLevinSituationTests.lean`.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Situation

open MetaMathlibExt

open Turing Function

/-! ## [B3] The symbolic effect of one statement tree, computed from windows only -/

section Eff

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- **Top of a stack as read from the windows.** Let $W$ assign to each stack $k$ a window, a list
of entries that are symbols of $k$ or the empty cell $\bot$; let $P$ assign to each stack $k$ a
list of symbols of $k$; and let $c$ assign a natural number to each stack. The top of stack $k$ is
the first element of $P(k)$ when $P(k)$ is nonempty. Otherwise it is the entry of $W(k)$ at
position $c(k)$, counting from $0$, or $\bot$ when $W(k)$ has fewer than $c(k) + 1$ entries.

Here $P(k)$ lists the symbols pushed in this step and still on top, and $c(k)$ counts the original
symbols already consumed. -/
def readTop (W : ∀ k, List (Option (Γ k))) (P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K) :
    Option (Γ k) :=
  match P k with
  | x :: _ => some x
  | [] => (W k).getD (c k) none

/-- **Symbolic effect of a statement tree.** Let $W$ assign to each stack $k$ a window $W_k$, a
list of cells each holding a symbol or $\bot$. The window top of stack $k$ for pushed lists $P$
and consumption counts $c$ is the head of $P_k$ if $P_k$ is nonempty, and otherwise the entry of
$W_k$ at position $c_k$ (counting from $0$), or $\bot$ if there is none. The effect of a statement
tree $q$ from a state $v$, pushed lists $P$ and consumption counts $c$ is a label (or none), a
state, pushed lists and consumption counts, defined by recursion on $q$: a push onto stack $k$
prepends the symbol computed from $v$ to $P_k$ and continues; a peek on stack $k$ replaces $v$ by
the state computed from $v$ and the window top of $k$ and continues; a pop on stack $k$ does the
same, also removes the head of $P_k$ (if any), and increases $c_k$ by one if $P_k$ was empty;
a load replaces $v$ by the state computed from $v$ and continues; a branch continues with the
subtree selected by $v$; a goto returns the label computed from $v$, and a halt returns no
label, each together with the current $v$, $P$ and $c$.

Thus $P_k$ holds the symbols pushed in this step and still on top, and $c_k$ counts the original
symbols consumed, a push followed by a pop cancelling. -/
def eff (W : ∀ k, List (Option (Γ k))) :
    TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → (K → ℕ) →
      Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)
  | .push k f q, v, P, c => eff W q v (update P k (f v :: P k)) c
  | .peek k f q, v, P, c => eff W q (f v (readTop W P c k)) P c
  | .pop k f q, v, P, c =>
      eff W q (f v (readTop W P c k)) (update P k (P k).tail)
        (if (P k).isEmpty then update c k (c k + 1) else c)
  | .load a q, v, P, c => eff W q (a v) P c
  | .branch p q₁ q₂, v, P, c => cond (p v) (eff W q₁ v P c) (eff W q₂ v P c)
  | .goto f, v, P, c => (some (f v), v, P, c)
  | .halt, v, P, c => (none, v, P, c)

/-- **Stack operations on a path of a statement tree.** For a statement tree $q$ of a multi-stack
Turing machine, $\operatorname{ops}(q)$ is the largest number of push, peek and pop nodes on a path
from the root of $q$ to a leaf. Load and branch nodes do not count, and goto and halt leaves
contribute $0$. -/
def ops : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => ops q + 1
  | .peek _ _ q => ops q + 1
  | .pop _ _ q => ops q + 1
  | .load _ q => ops q
  | .branch _ q₁ q₂ => max (ops q₁) (ops q₂)
  | .goto _ => 0
  | .halt => 0

/-- **Symbols a statement tree can push.** Let $q$ be a statement tree of a multi-stack Turing
machine with state type $\sigma$, let $k$ be a stack and $x$ a symbol of the alphabet of $k$. Then
$x$ can be pushed onto $k$ by $q$ when $q$ contains a push node onto stack $k$ with symbol
function $f$ and some state $v \in \sigma$ satisfies $x = f(v)$. Every push node of $q$ counts,
whichever branches are taken. -/
def PushSym (k : K) : TM2.Stmt Γ Λ σ → Γ k → Prop
  | .push k' f q, x => (∃ (h : k' = k) (v : σ), x = cast (congrArg Γ h) (f v)) ∨ PushSym k q x
  | .peek _ _ q, x => PushSym k q x
  | .pop _ _ q, x => PushSym k q x
  | .load _ q, x => PushSym k q x
  | .branch _ q₁ q₂, x => PushSym k q₁ x ∨ PushSym k q₂ x
  | .goto _, _ => False
  | .halt, _ => False

theorem length_update_le (P : ∀ k, List (Γ k)) (k₀ k : K) (l : List (Γ k₀))
    (h : l.length ≤ (P k₀).length + 1) : (update P k₀ l k).length ≤ (P k).length + 1 := by
  by_cases hk : k = k₀
  · subst hk; simpa using h
  · rw [update_of_ne hk]; omega

/-- **The symbolic effect grows by at most the number of stack operations.** Let $q$ be a statement
tree, let $W$ assign to each stack a window (a list of cells, each a symbol or $\bot$), and let
$n(q)$ be the largest number of push, peek and pop nodes on a root-to-leaf path of $q$. For every
state $v$, pushed lists $P$ and consumption counts $c$, the pushed lists $P'$ and consumption
counts $c'$ of the symbolic effect of $q$ on $W$ from $v$, $P$, $c$ satisfy
$|P'_k| \le |P_k| + n(q)$ and $c'_k \le c_k + n(q)$ for every stack $k$. -/
theorem eff_bound (W : ∀ k, List (Option (Γ k))) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K),
      ((eff W q v P c).2.2.1 k).length ≤ (P k).length + ops q ∧
        (eff W q v P c).2.2.2 k ≤ c k + ops q := by
  induction q with
  | push k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih v (update P k₀ (f v :: P k₀)) c k
      have := length_update_le P k₀ k (f v :: P k₀) (by simp)
      simp only [eff, ops]; omega
  | peek k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih (f v (readTop W P c k₀)) P c k
      simp only [eff, ops]; omega
  | pop k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih (f v (readTop W P c k₀)) (update P k₀ (P k₀).tail)
        (if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c) k
      have e1 := length_update_le P k₀ k (P k₀).tail (by simp; omega)
      have e2 : (if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c) k ≤ c k + 1 := by
        split
        · by_cases hk : k = k₀
          · subst hk; simp
          · rw [update_of_ne hk]; omega
        · omega
      simp only [eff, ops]; omega
  | load a q ih =>
      intro v P c k
      exact ih (a v) P c k
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c k
      simp only [eff, ops]
      cases p v
      · obtain ⟨h1, h2⟩ := ih₂ v P c k; simp only [Bool.cond_false]; omega
      · obtain ⟨h1, h2⟩ := ih₁ v P c k; simp only [Bool.cond_true]; omega
  | goto f => intro v P c k; simp [eff]
  | halt => intro v P c k; simp [eff]

/-- **Pushed symbols come from the start or from push nodes.** Let $q$ be a statement tree, let $W$
assign to each stack a window, and for each stack $k$ let $Q_k$ be a property of symbols of
stack $k$ such that every symbol that some push node of $q$ can push onto stack $k$, for some
state, satisfies $Q_k$. Then for every state $v$, pushed lists $P$ and consumption counts $c$
such that every symbol of $P_k$ satisfies $Q_k$ for every stack $k$, every symbol of the pushed
list on stack $k$ produced by the symbolic effect of $q$ on $W$ from $v$, $P$, $c$ satisfies
$Q_k$, for every stack $k$. -/
theorem eff_pushed (W : ∀ k, List (Option (Γ k))) (Q : ∀ k, Γ k → Prop) (q : TM2.Stmt Γ Λ σ)
    (hq : ∀ k x, PushSym k q x → Q k x) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ), (∀ k, ∀ x ∈ P k, Q k x) →
      ∀ k, ∀ x ∈ (eff W q v P c).2.2.1 k, Q k x := by
  induction q with
  | push k₀ f q ih =>
      intro v P c hP
      refine ih (fun k x h => hq k x (Or.inr h)) v _ c ?_
      intro k x hx
      by_cases hk : k = k₀
      · subst hk
        rw [update_self, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hq k (f v) (Or.inl ⟨rfl, v, rfl⟩)
        · exact hP k x hx
      · rw [update_of_ne hk] at hx; exact hP k x hx
  | peek k₀ f q ih =>
      intro v P c hP; exact ih hq _ P c hP
  | pop k₀ f q ih =>
      intro v P c hP
      refine ih hq _ _ _ ?_
      intro k x hx
      by_cases hk : k = k₀
      · subst hk
        rw [update_self] at hx
        exact hP k x (List.mem_of_mem_tail hx)
      · rw [update_of_ne hk] at hx; exact hP k x hx
  | load a q ih =>
      intro v P c hP; exact ih hq _ P c hP
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c hP
      simp only [eff]
      cases p v
      · exact ih₂ (fun k x h => hq k x (Or.inr h)) v P c hP
      · exact ih₁ (fun k x h => hq k x (Or.inl h)) v P c hP
  | goto f => intro v P c hP; exact hP
  | halt => intro v P c hP; exact hP

end Eff

/-! ## [B3] Encoding data for a real machine -/

/-- **Encoding data for a finite TM2 machine.** An encoding of a finite TM2 machine $M$ consists
of a number $K$, a map $\kappa$ from the stacks of $M$ to the naturals below $K$ and a map
$\kappa'$ from naturals to stacks with $\kappa'(\kappa(k)) = k$ for every stack $k$ and
$\kappa(\kappa'(n)) = n$ for every $n < K$; a number $A_0$, a map $\lambda$ from pairs (label
or halted, state) to the naturals below $A_0$ and a map $\lambda'$ back with
$\lambda'(\lambda(x)) = x$ for every pair $x$ and $\lambda(\lambda'(a)) = a$ for every
$a < A_0$; and for each stack $k$ a size $s_k$, effective symbols $d_k(i)$ for $i < s_k$, and a
symbol code map $e_k$ on the alphabet of stack $k$ with $e_k(d_k(i)) = i + 1$. It is required
that every symbol that a push node of the statement tree of some label can push onto stack $k$,
for some state, is an effective symbol of stack $k$, and that every symbol of the input stack's
alphabet is an effective symbol of the input stack.

Symbol code $0$ stands for $\bot$, the empty cell. -/
structure Enc (M : FinTM2) where
  /-- Number of stacks. -/
  KK : ℕ
  /-- Stack numbering. -/
  kc : M.K → ℕ
  /-- Inverse of the stack numbering. -/
  kd : ℕ → M.K
  kc_lt : ∀ k, kc k < KK
  kd_kc : ∀ k, kd (kc k) = k
  kc_kd : ∀ n < KK, kc (kd n) = n
  /-- Number of (label, state) codes. -/
  A0 : ℕ
  /-- (Label, state) numbering. -/
  lc : Option M.Λ × M.σ → ℕ
  /-- Inverse of the (label, state) numbering. -/
  ld : ℕ → Option M.Λ × M.σ
  lc_lt : ∀ x, lc x < A0
  ld_lc : ∀ x, ld (lc x) = x
  lc_ld : ∀ c < A0, lc (ld c) = c
  /-- Size of the effective alphabet of each stack. -/
  sz : M.K → ℕ
  /-- The effective symbols of each stack. -/
  dec : ∀ k, Fin (sz k) → M.Γ k
  /-- Symbol codes (`1 + index`; `0` is the empty cell). -/
  enc : ∀ k, M.Γ k → ℕ
  enc_dec : ∀ k i, enc k (dec k i) = i + 1
  push_mem : ∀ l k x, PushSym k (M.m l) x → ∃ i, dec k i = x
  input_mem : ∀ x : M.Γ M.k₀, ∃ i, dec M.k₀ i = x

/-- **Window depth of a machine.** For a finite TM2 machine $M$, the window depth is the maximum,
over all labels $l$ of $M$, of the largest number of push, peek and pop nodes on a root-to-leaf
path of the statement tree of $l$. -/
def depth (M : FinTM2) : ℕ :=
  letI := M.ΛFin
  Finset.univ.sup fun l => ops (M.m l)

theorem ops_le_depth (M : FinTM2) (l : M.Λ) : ops (M.m l) ≤ depth M := by
  letI := M.ΛFin
  exact Finset.le_sup (f := fun l => ops (M.m l)) (Finset.mem_univ l)

/-- **The situation step.** Let $M$ be a finite multi-stack Turing machine, let $l$ be either a
label of $M$ or $\mathrm{none}$ (the halted label), let $v$ be a state of $M$, and let $W$ assign
to each stack $k$ a window, a list of entries that are symbols of $k$ or the empty cell. If
$l = \mathrm{none}$, the step returns the label $\mathrm{none}$, the state $v$, no pushed symbols on
any stack and no consumed symbols on any stack. If $l$ is a label, the step is the effect, read
from the windows $W$, of the statement tree of $l$ started in state $v$ with nothing pushed and
nothing consumed. -/
def sitStep (M : FinTM2) (l : Option M.Λ) (v : M.σ) (W : ∀ k, List (Option (M.Γ k))) :
    Option M.Λ × M.σ × (∀ k, List (M.Γ k)) × (M.K → ℕ) :=
  match l with
  | none => (none, v, fun _ => [], fun _ => 0)
  | some l => eff W (M.m l) v (fun _ => []) (fun _ => 0)

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Symbol-code bound.** For an encoding $E$ of a finite TM2 machine $M$, the symbol-code bound
is $g = 1 + \max_k s_k$, where the maximum runs over all stacks $k$ of $M$ and $s_k$ is the size
of the effective alphabet of stack $k$.

Effective symbols of stack $k$ have codes $1, \dots, s_k$, all below $g$; code $0$ is $\bot$. -/
def g : ℕ :=
  letI := M.kFin
  1 + Finset.univ.sup E.sz

/-- **Number of window combinations.** For an encoding $E$ of a finite TM2 machine $M$ with $K$
numbered stacks and symbol-code bound $g$, the number of window combinations is $G = g^{K d}$,
where $d$ is the window depth of $M$. -/
def G : ℕ := E.g ^ (E.KK * depth M)

/-- **Number of situations.** For an encoding $E$ of a finite multi-stack Turing machine $M$, the
number of situations is $N = A_0 \cdot G$, where $A_0$ is the number of (label, state) codes of
$E$ and $G$ is the number of window combinations. -/
def N : ℕ := E.A0 * E.G

/-- **Clause layout of a machine encoding.** For an encoding $E$ of a finite TM2 machine $M$, the
layout of the transition clauses has label/state block size $A = A_0 + N$, where $A_0$ is the
number of label/state codes and $N = A_0 G$ is the number of situations ($G$ the number of
window combinations), together with the number $K$ of numbered stacks, the symbol-code bound $g$
and the window depth $d$ of $M$. The block is a one-hot part on $[0, A_0)$ followed by one
variable per situation. -/
def layout : Family.Layout := ⟨E.A0 + E.N, E.KK, E.g, depth M⟩

/-! ### The tables (situation `i` in mixed radix: digits `k·d + j` = windows, top = code) -/

/-- **Label/state code of a situation.** For an encoding $E$ of a finite TM2 machine with $A_0$
label/state codes and $G$ window combinations, the label/state code of a situation
$i \in \mathbb{N}$ is $\lfloor i / G \rfloor \bmod A_0$, the top digit of $i$ in the mixed radix
whose lower digits are the window symbol codes. -/
def la (i : ℕ) : ℕ := i / E.G % E.A0

/-- **Window symbol code of a situation.** Let $E$ be an encoding of a finite multi-stack Turing
machine $M$, let $s_\kappa$ be the size of the effective alphabet of stack $\kappa$ in $E$, let
$g = 1 + \max_\kappa s_\kappa$ (so the empty-cell code $0$ and every effective symbol code are
below $g$), and let $d$ be the window depth of $M$. For natural numbers $i$, $k$ and $j$, the
window symbol code of situation $i$ on stack number $k$ at depth $j$ is the base-$g$ digit of $i$
at position $kd + j$, namely $\lfloor i / g^{kd + j} \rfloor \bmod g$. -/
def wa (i k j : ℕ) : ℕ := i / E.g ^ (k * depth M + j) % E.g

/-- **Position of a situation's variable.** For an encoding $E$ of a finite multi-stack Turing
machine $M$ with $A_0$ (label, state) codes and a natural number $i$, the variable of situation
$i$ sits at position $A_0 + i$ of the label/state block of a row. -/
def sa (i : ℕ) : ℕ := E.A0 + i

/-- **Decoding a symbol code.** For an encoding $E$ of a finite TM2 machine $M$, a stack $k$
and a natural number $c$, the decoded symbol is the effective symbol of stack $k$ with index
$c - 1$ when $1 \le c$ and $c - 1 < s_k$, where $s_k$ is the size of the effective alphabet of
stack $k$; otherwise, in particular for $c = 0$, it is $\bot$ (no symbol). -/
def decO (k : M.K) (c : ℕ) : Option (M.Γ k) :=
  if h : 1 ≤ c ∧ c - 1 < E.sz k then some (E.dec k ⟨c - 1, h.2⟩) else none

/-- **Decoded windows of a situation.** Let $E$ be an encoding of a finite multi-stack Turing
machine $M$ with window depth $d$, and let $i$ be a natural number. The window of situation $i$ on
stack $k$ is the list of length $d$ whose entry at position $j < d$ decodes the window symbol code
$c$ of situation $i$ on the stack number of $k$ at depth $j$. A code with $1 \le c \le s_k$, where
$s_k$ is the size of the effective alphabet of $k$, decodes to the effective symbol of $k$ with
index $c - 1$; every other code decodes to the empty cell $\bot$. -/
def win (i : ℕ) : ∀ k, List (Option (M.Γ k)) := fun k =>
  (List.range (depth M)).map fun j => E.decO k (E.wa i (E.kc k) j)

/-- **Effect of a situation.** Let $E$ be an encoding of a finite multi-stack Turing machine $M$
and $i$ a natural number. Let $(l, v)$, an optional label and a state, be the result of decoding
the label/state code of situation $i$ with the inverse (label, state) numbering of $E$, and let
$W$ be the decoded windows of situation $i$. The effect of situation $i$ is the situation step of
$M$ from $l$, $v$ and $W$: a new optional label, a new state, the symbols left pushed on each
stack, and the number of original symbols consumed from each stack. -/
def res (i : ℕ) : Option M.Λ × M.σ × (∀ k, List (M.Γ k)) × (M.K → ℕ) :=
  sitStep M (E.ld (E.la i)).1 (E.ld (E.la i)).2 (E.win i)

/-- **Next label/state code of a situation.** For an encoding $E$ of a finite multi-stack Turing
machine $M$ and a natural number $i$, the next label/state code of situation $i$ is the code, in
the (label, state) numbering of $E$, of the pair formed by the label and the state that the effect
of situation $i$ produces. -/
def na (i : ℕ) : ℕ := E.lc ((E.res i).1, (E.res i).2.1)

/-- **Push-count table of a situation.** Fix an encoding record $E$ of a finite multi-stack
machine. For a situation $i$ and a stack number $k$, $\mathrm{pl}(i, k)$ is the number of symbols
that the effect of situation $i$ has pushed onto the stack that the inverse stack numbering of $E$
assigns to $k$ and that are still on top of that stack at the end of the step. -/
def pl (i k : ℕ) : ℕ := ((E.res i).2.2.1 (E.kd k)).length

/-- **Consumption table of a situation.** Fix an encoding record $E$ of a finite multi-stack
machine. For a situation $i$ and a stack number $k$, $\mathrm{cn}(i, k)$ is the number of original
symbols that the effect of situation $i$ consumes from the stack that the inverse stack numbering
of $E$ assigns to $k$; a symbol pushed and then popped within the same step is not counted. -/
def cn (i k : ℕ) : ℕ := (E.res i).2.2.2 (E.kd k)

/-- **Pushed-symbol table of a situation.** Fix an encoding record $E$ of a finite multi-stack
machine. For a situation $i$, a stack number $k$ and a depth $j$, $\mathrm{pu}(i, k, j)$ is the
code of the symbol at position $j$ from the top (counting from $0$) among the symbols that the
effect of situation $i$ leaves pushed on the stack that the inverse stack numbering of $E$ assigns
to $k$, and $0$ if fewer than $j + 1$ symbols are left pushed there. -/
def pu (i k j : ℕ) : ℕ := (((E.res i).2.2.1 (E.kd k))[j]?).elim 0 (E.enc (E.kd k))

/-! ### Well-formedness -/

/-- **The symbol-code bound is positive.** For an encoding $E$ of a finite TM2 machine, the
symbol-code bound $g$ of $E$ satisfies $0 < g$. -/
theorem g_pos : 0 < E.g := by unfold g; omega

theorem sz_lt_g (k : M.K) : E.sz k < E.g := by
  letI := M.kFin
  have := Finset.le_sup (f := E.sz) (Finset.mem_univ k)
  unfold g; omega

theorem A0_pos : 0 < E.A0 := Nat.lt_of_le_of_lt (Nat.zero_le _) (E.lc_lt (none, M.initialState))

theorem la_lt (i : ℕ) : E.la i < E.A0 := Nat.mod_lt _ E.A0_pos

theorem na_lt (i : ℕ) : E.na i < E.A0 := E.lc_lt _

theorem wa_lt (i k j : ℕ) : E.wa i k j < E.g := Nat.mod_lt _ E.g_pos

theorem res_bound (i : ℕ) (k : M.K) :
    ((E.res i).2.2.1 k).length ≤ depth M ∧ (E.res i).2.2.2 k ≤ depth M := by
  unfold res sitStep
  split
  · simp
  · next l _ =>
    have := eff_bound (E.win i) (M.m l) (E.ld (E.la i)).2 (fun _ => []) (fun _ => 0) k
    have := ops_le_depth M l
    simp only [List.length_nil] at *; omega

theorem pl_le (i k : ℕ) : E.pl i k ≤ depth M := (E.res_bound i (E.kd k)).1

theorem cn_le (i k : ℕ) : E.cn i k ≤ depth M := (E.res_bound i (E.kd k)).2

/-- **Symbols left pushed by a situation are effective.** Let $E$ be an encoding of a finite
multi-stack Turing machine $M$, and for each stack $k$ of $M$ let $s_k$ be the size of the
effective alphabet of stack $k$ in $E$ and $\mathrm{dec}_k(n)$, for $n < s_k$, its $n$-th
effective symbol. For every $i \in \mathbb{N}$, every stack $k$ of $M$ and every symbol $x$ of the
alphabet of stack $k$: if $x$ is among the symbols that the effect of situation $i$ leaves pushed
on stack $k$, then $x = \mathrm{dec}_k(n)$ for some $n < s_k$. -/
theorem res_pushed (i : ℕ) (k : M.K) (x : M.Γ k) (hx : x ∈ (E.res i).2.2.1 k) :
    ∃ n, E.dec k n = x := by
  unfold res sitStep at hx
  split at hx
  · simp at hx
  · next l _ =>
    exact eff_pushed (E.win i) (fun k x => ∃ n, E.dec k n = x) (M.m l)
      (fun k x h => E.push_mem l k x h) _ _ _ (fun _ _ h => by simp at h) k x hx

theorem decO_succ (k : M.K) (n : Fin (E.sz k)) : E.decO k (n + 1) = some (E.dec k n) := by
  unfold decO
  rw [dite_eq_left ⟨by omega, by simp⟩]
  simp

/-- **Pushed codes are valid symbol codes.** Fix an encoding record $E$ of a finite multi-stack
machine. Let $i$ be a situation, $k$ a stack number, $s$ the stack that the inverse stack numbering
of $E$ assigns to $k$, $n_s$ the size of the effective alphabet of $s$, and $j < \mathrm{pl}(i, k)$.
Then there is a symbol $x$ at position $j$ from the top (counting from $0$) among the symbols the
effect of situation $i$ leaves pushed on $s$, such that $\mathrm{pu}(i, k, j)$ is the code of $x$,
$1 \le \mathrm{pu}(i, k, j) \le n_s$, and decoding $\mathrm{pu}(i, k, j)$ on stack $s$ gives $x$. -/
theorem pu_valid (i k j : ℕ) (hj : j < E.pl i k) :
    ∃ x, ((E.res i).2.2.1 (E.kd k))[j]? = some x ∧ E.pu i k j = E.enc (E.kd k) x ∧
      1 ≤ E.pu i k j ∧ E.pu i k j ≤ E.sz (E.kd k) ∧ E.decO (E.kd k) (E.pu i k j) = some x := by
  unfold pl at hj
  obtain ⟨x, hx⟩ : ∃ x, ((E.res i).2.2.1 (E.kd k))[j]? = some x :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  have hmem : x ∈ (E.res i).2.2.1 (E.kd k) := List.mem_of_getElem? hx
  obtain ⟨n, rfl⟩ := E.res_pushed i _ x hmem
  have hpu : E.pu i k j = n + 1 := by unfold pu; rw [hx]; simp [E.enc_dec]
  refine ⟨_, hx, by rw [hpu, E.enc_dec], by omega, by have := n.2; omega, ?_⟩
  rw [hpu]; exact E.decO_succ _ n

theorem pu_lt (i k j : ℕ) (hj : j < E.pl i k) : E.pu i k j < E.g := by
  obtain ⟨_, _, _, _, h, _⟩ := E.pu_valid i k j hj
  have := E.sz_lt_g (E.kd k); omega

/-- **The transition tables of a machine are well formed.** Let $M$ be a finite multi-stack
Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$ label/state codes,
$K$ stacks, $g$ symbol codes and $N$ situations, and let $H \ge d$. For every $i \in \mathbb{N}$,
the current-code table $\mathrm{la}$, the next-code table $\mathrm{na}$ and the window table
$\mathrm{wa}$ of $E$ are well formed for the transition clauses of the layout of $E$ at situation
$i$ and height $H$: that is, $\mathrm{la}(i) < A_0 + N$, $\mathrm{na}(i) < A_0 + N$,
$\mathrm{wa}(i, k, j) < g$ for all $k < K$ and $j < d$, and $d \le H$. -/
theorem wf_upd {H : ℕ} (hH : depth M ≤ H) (i : ℕ) : Family.WF E.layout E.la E.na E.wa H i :=
  ⟨by have := E.la_lt i; simp only [layout]; omega,
   by have := E.na_lt i; simp only [layout]; omega,
   fun k _ j _ => E.wa_lt i k j, hH⟩

/-- **The situation-definition tables of a machine are well formed.** Let $M$ be a finite
multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$
label/state codes, $K$ stacks, $g$ symbol codes and $N$ situations, and let $H \ge d$. For every
situation $i < N$, the current-code table $\mathrm{la}$ of $E$, the table
$\mathrm{sa}(i) = A_0 + i$ as next-code table and the window table $\mathrm{wa}$ of $E$ are well
formed for the transition clauses of the layout of $E$ at situation $i$ and height $H$: that is,
$\mathrm{la}(i) < A_0 + N$, $\mathrm{sa}(i) < A_0 + N$, $\mathrm{wa}(i, k, j) < g$ for all
$k < K$ and $j < d$, and $d \le H$. -/
theorem wf_sdef {H : ℕ} (hH : depth M ≤ H) (i : ℕ) (hi : i < E.N) :
    Family.WF E.layout E.la E.sa E.wa H i :=
  ⟨by have := E.la_lt i; simp only [layout]; omega,
   by simp only [layout, sa]; omega,
   fun k _ j _ => E.wa_lt i k j, hH⟩

/-- **The cell-shift tables of a machine are well formed.** Let $M$ be a finite multi-stack Turing
machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$ label/state codes, $K$
stacks, $g$ symbol codes and $N$ situations, and let $H \ge d$. Then the table
$\mathrm{sa}(i) = A_0 + i$, the push counts $\mathrm{pl}$, the consumption counts $\mathrm{cn}$
and the pushed codes $\mathrm{pu}$ of $E$ are well formed for the cell-shift clauses of the layout
of $E$ with $N$ situations at height $H$: that is, $0 < g$, $d \le H$,
$\mathrm{sa}(i) < A_0 + N$ for all $i < N$, and for all $i < N$ and $k < K$ we have
$\mathrm{pl}(i, k) \le d$, $\mathrm{cn}(i, k) \le d$ and $\mathrm{pu}(i, k, j) < g$ for all
$j < \mathrm{pl}(i, k)$. -/
theorem wf_sh {H : ℕ} (hH : depth M ≤ H) : Shift.WF E.layout E.sa E.pl E.cn E.pu E.N H :=
  ⟨E.g_pos, hH, fun i hi => by simp only [layout, sa]; omega,
   fun i _ k _ => E.pl_le i k, fun i _ k _ => E.cn_le i k,
   fun i _ k _ j hj => E.pu_lt i k j hj⟩

/-! ### Halted situations -/

/-- **Halted situations stay fixed.** If the (label, state) pair decoded from the code
$\mathrm{la}(i)$ of situation $i$ has no label, so the machine has halted, then for every stack
number $k$ the next code equals the current one, $\mathrm{na}(i) = \mathrm{la}(i)$, and
$\mathrm{pl}(i, k) = 0$ and $\mathrm{cn}(i, k) = 0$: nothing is left pushed and nothing is
consumed. -/
theorem halted (i : ℕ) (h : (E.ld (E.la i)).1 = none) (k : ℕ) :
    E.na i = E.la i ∧ E.pl i k = 0 ∧ E.cn i k = 0 := by
  have hr : E.res i = (none, (E.ld (E.la i)).2, fun _ => [], fun _ => 0) := by
    unfold res sitStep; rw [h]
  refine ⟨?_, by simp [pl, hr], by simp [cn, hr]⟩
  unfold na; rw [hr]
  have : ((none : Option M.Λ), (E.ld (E.la i)).2) = E.ld (E.la i) := by
    rw [← h]
  rw [this, E.lc_ld _ (E.la_lt i)]

/-! ### Every (code, windows) pair is a situation `i < N` (mixed radix; C6 needs it) -/

/-- **Mixed-radix number.** For a base $b$, a top digit $c$, a length $m$ and digits
$D : \mathbb{N} \to \mathbb{N}$, $\mathrm{mix}(b, c, 0, D) = c$ and
$\mathrm{mix}(b, c, m + 1, D) = D(0) + b \cdot \mathrm{mix}(b, c, m, n \mapsto D(n + 1))$; that
is, $D(0) + b\,(D(1) + b\,(\cdots + b\,(D(m - 1) + b\,c)))$, least significant digit first. -/
def mix (b c : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => c
  | m + 1, D => D 0 + b * mix b c m (fun n => D (n + 1))

theorem mix_spec (b c : ℕ) : ∀ (m : ℕ) (D : ℕ → ℕ), (∀ n < m, D n < b) →
    (∀ n < m, mix b c m D / b ^ n % b = D n) ∧ mix b c m D / b ^ m = c ∧
      mix b c m D < (c + 1) * b ^ m := by
  intro m
  induction m with
  | zero => intro D _; simp [mix]
  | succ m ih =>
      intro D hD
      obtain ⟨h1, h2, h3⟩ := ih (fun n => D (n + 1)) (fun n hn => hD (n + 1) (by omega))
      have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) (hD 0 (by omega))
      have h0 := hD 0 (by omega)
      have hdiv : (D 0 + b * mix b c m (fun n => D (n + 1))) / b =
          mix b c m (fun n => D (n + 1)) := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h0, Nat.zero_add]
      simp only [mix]
      refine ⟨?_, ?_, ?_⟩
      · intro n hn
        cases n with
        | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
        | succ n =>
            rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]; exact h1 n (by omega)
      · rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv, h2]
      · have : b * (mix b c m (fun n => D (n + 1)) + 1) ≤ b * ((c + 1) * b ^ m) :=
          Nat.mul_le_mul_left _ h3
        rw [pow_succ']
        have e : b * ((c + 1) * b ^ m) = (c + 1) * (b * b ^ m) := by ring
        rw [Nat.mul_add, e] at this; omega

/-- **Mixed-radix index of a situation.** Fix an encoding record $E$ of a finite multi-stack
machine $M$. Let $K$ be the number of stacks of $E$, $d$ the window depth of $M$, $A_0$ the number
of (label, state) codes of $E$, $g$ the symbol-code bound of $E$ and $N$ the number of situations.
For a code $c < A_0$ and window contents $w(k, j)$ with $w(k, j) < g$ for all $k < K$ and $j < d$,
let $i = \mathrm{mix}(g, c, K d, D)$ with digits $D(n) = w(\lfloor n / d \rfloor, n \bmod d)$.
Then $i < N$, $\mathrm{la}(i) = c$, and $\mathrm{wa}(i, k, j) = w(k, j)$ for all $k < K$ and
$j < d$. -/
theorem mix_sit (c : ℕ) (hc : c < E.A0) (w : ℕ → ℕ → ℕ)
    (hw : ∀ k < E.KK, ∀ j < depth M, w k j < E.g) :
    mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M)) < E.N ∧
    E.la (mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M))) = c ∧
    ∀ k < E.KK, ∀ j < depth M,
      E.wa (mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M))) k j = w k j := by
  set d := depth M
  have hD : ∀ n < E.KK * d, (fun n => w (n / d) (n % d)) n < E.g := by
    intro n hn
    have hd : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hn
    exact hw _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn)) _ (Nat.mod_lt _ hd)
  obtain ⟨h1, h2, h3⟩ := mix_spec E.g c (E.KK * d) _ hD
  refine ⟨?_, ?_, ?_⟩
  · have h3' : _ < (c + 1) * E.G := h3
    exact Nat.lt_of_lt_of_le h3' (Nat.mul_le_mul_right _ hc)
  · unfold la G; rw [h2, Nat.mod_eq_of_lt hc]
  · intro k hk j hj
    have hkj : k * d + j < E.KK * d := by
      have : (k + 1) * d ≤ E.KK * d := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at this; omega
    unfold wa; rw [h1 _ hkj]
    have hd : 0 < d := by omega
    have e1 : (k * d + j) / d = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (k * d + j) % d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

/-- **Situation surjectivity.** Let $E$ be an encoding of a finite multi-stack Turing machine $M$
with $A_0$ label/state codes, $K$ stacks, $g$ symbol codes, window depth $d$ and $N$ situations.
For every $c < A_0$ and every $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ with $w(k, j) < g$
for all $k < K$ and $j < d$, there is a situation $i < N$ whose label/state code
$\mathrm{la}(i)$ equals $c$ and whose window codes satisfy $\mathrm{wa}(i, k, j) = w(k, j)$ for
all $k < K$ and $j < d$. -/
theorem sit_surj (c : ℕ) (hc : c < E.A0) (w : ℕ → ℕ → ℕ)
    (hw : ∀ k < E.KK, ∀ j < depth M, w k j < E.g) :
    ∃ i < E.N, E.la i = c ∧ ∀ k < E.KK, ∀ j < depth M, E.wa i k j = w k j :=
  ⟨_, E.mix_sit c hc w hw⟩

end Enc

/-! ## [B2] A classical `Enc` for every `FinTM2` -/

section Classical

open Classical

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Fintype σ]

/-- **Finite set of pushable symbols.** For a stack $k$ and a statement tree $q$ of a multi-stack
machine with a finite set of states, the finite set of symbols of stack $k$ that some push
instruction of $q$ on stack $k$ pushes for some state: the union, over all push instructions on
$k$ in all branches of $q$, of the images of their push functions over all states. -/
noncomputable def pushFS (k : K) : TM2.Stmt Γ Λ σ → Finset (Γ k)
  | .push k' f q =>
      (if h : k' = k then Finset.univ.image fun v => cast (congrArg Γ h) (f v) else ∅) ∪
        pushFS k q
  | .peek _ _ q => pushFS k q
  | .pop _ _ q => pushFS k q
  | .load _ q => pushFS k q
  | .branch _ q₁ q₂ => pushFS k q₁ ∪ pushFS k q₂
  | .goto _ => ∅
  | .halt => ∅

theorem mem_pushFS (k : K) (q : TM2.Stmt Γ Λ σ) (x : Γ k) (h : PushSym k q x) :
    x ∈ pushFS k q := by
  induction q with
  | push k' f q ih =>
      simp only [PushSym] at h
      simp only [pushFS, Finset.mem_union]
      rcases h with ⟨rfl, v, rfl⟩ | h
      · left; rw [dite_eq_left rfl]; exact Finset.mem_image_of_mem _ (Finset.mem_univ v)
      · right; exact ih h
  | peek _ _ q ih => exact ih h
  | pop _ _ q ih => exact ih h
  | load _ q ih => exact ih h
  | branch _ q₁ q₂ ih₁ ih₂ =>
      simp only [PushSym] at h
      simp only [pushFS, Finset.mem_union]
      exact h.imp ih₁ ih₂
  | goto _ => exact h.elim
  | halt => exact h.elim

/-- **Pushable and input symbols of a stack.** For a finite multi-stack Turing machine $M$ and a
stack $k$ of $M$, this is the finite set of symbols of stack $k$ consisting of every symbol that
some push node on stack $k$ in the statement of some label of $M$ pushes in some state, together
with, when $k$ is the input stack $k_0$, every symbol of the alphabet of $k_0$. -/
noncomputable def symSet (M : FinTM2) (k : M.K) : Finset (M.Γ k) :=
  letI := M.ΛFin; letI := M.σFin; letI := M.Γk₀Fin
  (Finset.univ.biUnion fun l => pushFS k (M.m l)) ∪
    (if h : M.k₀ = k then Finset.univ.image fun x : M.Γ M.k₀ => cast (congrArg M.Γ h) x else ∅)

theorem push_mem_symSet (M : FinTM2) (l : M.Λ) (k : M.K) (x : M.Γ k)
    (h : PushSym k (M.m l) x) : x ∈ symSet M k := by
  letI := M.ΛFin; letI := M.σFin
  unfold symSet
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, mem_pushFS k _ x h⟩)

theorem input_mem_symSet (M : FinTM2) (x : M.Γ M.k₀) : x ∈ symSet M M.k₀ := by
  letI := M.Γk₀Fin
  unfold symSet
  refine Finset.mem_union_right _ ?_
  rw [dite_eq_left rfl]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- **The classical encoding record of a finite multi-stack machine.** For every finite
multi-stack Turing machine $M$, an encoding record of $M$, built with classical choice. If $M$ has
$K$ stacks, they are numbered $0, \dots, K - 1$ by a bijection, and numbers $n \ge K$ decode to the
input stack. The pairs of an optional label and a state are numbered $0, \dots, A_0 - 1$ by a
bijection, where $A_0$ is the number of such pairs, and numbers $c \ge A_0$ decode to the pair of
no label and the initial state. The effective alphabet of stack $k$ is the finite set of symbols
that some statement of $M$ can push on $k$, together with the whole input alphabet when $k$ is
the input stack; its $s_k$ elements are listed by a bijection with $\{0, \dots, s_k - 1\}$, a
symbol in it gets code its position in that list plus $1$, and a symbol outside it gets code $0$.

Only the existence of this record is used later. -/
noncomputable def Enc.ofFinTM2 (M : FinTM2) : Enc M :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { KK := Fintype.card M.K
    kc := fun k => Fintype.equivFin M.K k
    kd := fun n => if h : n < Fintype.card M.K then (Fintype.equivFin M.K).symm ⟨n, h⟩ else M.k₀
    kc_lt := fun k => (Fintype.equivFin M.K k).2
    kd_kc := fun k => by simp
    kc_kd := fun n hn => by simp [hn]
    A0 := Fintype.card (Option M.Λ × M.σ)
    lc := fun x => Fintype.equivFin _ x
    ld := fun c => if h : c < Fintype.card (Option M.Λ × M.σ) then
      (Fintype.equivFin _).symm ⟨c, h⟩ else (none, M.initialState)
    lc_lt := fun x => (Fintype.equivFin _ x).2
    ld_lc := fun x => by rw [dite_eq_left (Fintype.equivFin _ x).2]; simp
    lc_ld := fun c hc => by rw [dite_eq_left hc]; simp
    sz := fun k => (symSet M k).card
    dec := fun k i => ((symSet M k).equivFin.symm i).1
    enc := fun k x => if h : x ∈ symSet M k then (symSet M k).equivFin ⟨x, h⟩ + 1 else 0
    enc_dec := fun k i => by simp
    push_mem := fun l k x h => ⟨(symSet M k).equivFin ⟨x, push_mem_symSet M l k x h⟩, by simp⟩
    input_mem := fun x => ⟨(symSet M M.k₀).equivFin ⟨x, input_mem_symSet M x⟩, by simp⟩ }

end Classical

/-! ## [B3] The real tables feed the proved generators -/

section Gen

variable {M : FinTM2} (E : Enc M) {H : ℕ} (hH : depth M ≤ H)
include hH

open Cslib.Complexity.CookLevin.Family Cslib.Complexity.CookLevin.CounterView in
/-- **Time bound of the transition-clause generator on the tables of a machine.** Let $M$ be a
finite multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $N$
situations, and let $H \ge d$ and $T \in \mathbb{N}$. Run the transition-clause generator for the
layout of $E$, the current-code table $\mathrm{la}$, the next-code table $\mathrm{na}$ and the
window table $\mathrm{wa}$ of $E$ and $N$ situations, started at its first precomputation stage,
in state false, with $T$ on the time counter and $H$ on the height counter in unary, all other
counters empty, and an arbitrary list $o$ of bits on the output stack. Then within
$c\,(T + H + 1)^5$ steps, where $c$ is the constant of the generator's time bound for this layout
and $N$, it reaches its final label $\mathsf{done}$, in some state, with stacks whose output stack
holds the encoding of the transition clause family for this layout, $\mathrm{la}$, $\mathrm{na}$,
$\mathrm{wa}$, $T$, $H$ and $N$, followed by $o$. -/
theorem upd_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      TM2Program.RunLe (prog E.layout E.la E.na E.wa E.N) (genC E.layout E.N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (family E.layout E.la E.na E.wa T H E.N) ++ o :=
  gen_time T H (fun i _ => E.wf_upd hH i) o

open Cslib.Complexity.CookLevin.Family Cslib.Complexity.CookLevin.CounterView in
/-- **Time bound of the situation-definition generator on the tables of a machine.** Let $M$ be a
finite multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$
label/state codes and $N$ situations, and let $H \ge d$ and $T \in \mathbb{N}$. Run the
transition-clause generator for the layout of $E$, the current-code table $\mathrm{la}$ of $E$,
the table $\mathrm{sa}(i) = A_0 + i$ (the position of the variable of situation $i$) in place of
the next-code table, the window table $\mathrm{wa}$ of $E$ and $N$ situations, started at its
first precomputation stage, in state false, with $T$ on the time counter and $H$ on the height
counter in unary, all other counters empty, and an arbitrary list $o$ of bits on the output
stack. Then within $c\,(T + H + 1)^5$ steps, where $c$ is the constant of the generator's time
bound for this layout and $N$, it reaches its final label $\mathsf{done}$, in some state, with
stacks whose output stack holds the encoding of the transition clause family for this layout,
$\mathrm{la}$, $\mathrm{sa}$, $\mathrm{wa}$, $T$, $H$ and $N$, followed by $o$. -/
theorem sdef_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      TM2Program.RunLe (prog E.layout E.la E.sa E.wa E.N) (genC E.layout E.N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (family E.layout E.la E.sa E.wa T H E.N) ++ o :=
  gen_time T H (fun i hi => E.wf_sdef hH i hi) o

open Cslib.Complexity.CookLevin.Shift Cslib.Complexity.CookLevin.CounterView in
/-- **Time bound of the shift generator on the tables of a machine.** Let $M$ be a finite
multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$
label/state codes and $N$ situations, and let $H \ge d$ and $T \in \mathbb{N}$. Run the cell-shift
generator for the layout of $E$, the table $\mathrm{sa}(i) = A_0 + i$ (the position of the
variable of situation $i$), the push counts $\mathrm{pl}$, the consumption counts $\mathrm{cn}$
and the pushed codes $\mathrm{pu}$ of $E$ and $N$ situations, started at its first precomputation
stage, in state false, with $T$ on the time counter and $H$ on the height counter in unary, all
other counters empty, and an arbitrary list $o$ of bits on the output stack. Then within
$c\,(T + H + 1)^6$ steps, where $c$ is the constant of the shift-generator time bound for this
layout and $N$, it reaches its final label $\mathsf{done}$, in some state, with stacks whose
output stack holds the encoding of the cell-shift clause family for this layout, $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$, $N$, $T$ and $H$, followed by $o$. -/
theorem shift_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ Shift.CK k)),
      TM2Program.RunLe (Shift.prog E.layout E.sa E.pl E.cn E.pu E.N) (shC E.layout E.N * (T + H + 1) ^ 6)
        ⟨some (.pre .eg), false, CounterView.st (Shift.initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) ++ o :=
  sh_time T H (E.wf_sh hH) o

end Gen

/-! ## [B1] Agreement of the symbolic effect with Mathlib's `TM2.stepAux` -/

section Agree

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- **Top window of a stack.** For $d \in \mathbb{N}$ and a list $L = [x_0, x_1, \dots]$ over a
type $\alpha$ (a stack, top first), the window of depth $d$ of $L$ is the list of length $d$ over
$\alpha$ extended by the empty cell $\bot$ whose entry $j$ is $x_j$ if $j$ is less than the length
of $L$ and $\bot$ otherwise. -/
def window {α : Type} (d : ℕ) (L : List α) : List (Option α) :=
  (List.range d).map fun j => L[j]?

/-- **Applying an effect to the original stacks.** Let $S_0$ assign a list $S_0(k)$ to each stack
$k$, and let $r = (\ell, v, P, c)$ consist of a label $\ell$ (possibly the halted label), a state
$v$, a list $P(k)$ for each stack $k$ and a natural number $c(k)$ for each stack $k$. This is the
configuration with label $\ell$, state $v$, and stack $k$ equal to $P(k)$ followed by $S_0(k)$
with its first $c(k)$ symbols (from the top) removed.

Applied to an effect, $P(k)$ is the pushed prefix still on top of stack $k$ and $c(k)$ is the net
number of original symbols consumed. -/
def applyEff (S0 : ∀ k, List (Γ k)) (r : Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)) :
    TM2.Cfg Γ Λ σ :=
  ⟨r.1, r.2.1, fun k => r.2.2.1 k ++ (S0 k).drop (r.2.2.2 k)⟩

omit [DecidableEq K] in
/-- **Reading the top through the windows.** Let $d \in \mathbb{N}$, let $S_0$ and $P$ assign a list
to each stack, let $c$ assign a natural number to each stack, and let $k$ be a stack with
$c(k) < d$. Reading the top of stack $k$ from the depth-$d$ windows of the lists $S_0$, with pushed
symbols $P$ and consumption counts $c$, gives the first symbol of $P(k)$ followed by $S_0(k)$ with
its first $c(k)$ symbols removed, or ⊥ if that list is empty. -/
theorem readTop_eq (d : ℕ) (S0 P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K) (hc : c k < d) :
    readTop (fun k => window d (S0 k)) P c k = (P k ++ (S0 k).drop (c k)).head? := by
  unfold readTop
  cases P k with
  | cons x _ => rfl
  | nil =>
      simp [window, List.getD_eq_getElem?_getD, List.getElem?_range hc, List.head?_drop]

/-- **The symbolic effect of a statement agrees with the real step.** Let $q$ be a statement tree
of a multi-stack machine, $d \in \mathbb{N}$, and $S_0$ an assignment of a list $S_0(k)$ to each
stack $k$. Let $v$ be a state, $P$ an assignment of a list $P(k)$ to each stack, and $c$ an
assignment of a natural number $c(k)$ to each stack with $c(k) + \operatorname{ops}(q) \le d$ for
every $k$. Then running $q$ from state $v$ on the stacks whose stack $k$ is $P(k)$ followed by
$S_0(k)$ with its first $c(k)$ symbols removed gives the configuration obtained by applying to
$S_0$ the effect of $q$ computed from $v$, $P$, $c$ and the depth-$d$ windows of the $S_0(k)$.

Here $\operatorname{ops}(q)$ is the largest number of push, peek and pop nodes on a path of $q$,
so the hypothesis keeps every read inside the windows. -/
theorem eff_agree (d : ℕ) (S0 : ∀ k, List (Γ k)) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ), (∀ k, c k + ops q ≤ d) →
      TM2.stepAux q v (fun k => P k ++ (S0 k).drop (c k)) =
        applyEff S0 (eff (fun k => window d (S0 k)) q v P c) := by
  induction q with
  | push k₀ f q ih =>
      intro v P c hc
      have e : update (fun k => P k ++ (S0 k).drop (c k)) k₀
          (f v :: (P k₀ ++ (S0 k₀).drop (c k₀))) =
          fun k => update P k₀ (f v :: P k₀) k ++ (S0 k).drop (c k) := by
        funext k
        by_cases hk : k = k₀
        · subst hk; simp
        · simp [update_of_ne hk]
      simp only [TM2.stepAux, eff]
      rw [e]
      exact ih v _ c fun k => by have := hc k; simp only [ops] at this; omega
  | peek k₀ f q ih =>
      intro v P c hc
      have hk : c k₀ < d := by have := hc k₀; simp only [ops] at this; omega
      simp only [TM2.stepAux, eff]
      rw [← readTop_eq d S0 P c k₀ hk]
      exact ih _ P c fun k => by have := hc k; simp only [ops] at this; omega
  | pop k₀ f q ih =>
      intro v P c hc
      have hk : c k₀ < d := by have := hc k₀; simp only [ops] at this; omega
      set c' := if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c with hc'
      have e : update (fun k => P k ++ (S0 k).drop (c k)) k₀
          (P k₀ ++ (S0 k₀).drop (c k₀)).tail =
          fun k => update P k₀ (P k₀).tail k ++ (S0 k).drop (c' k) := by
        funext k
        by_cases hk : k = k₀
        · subst hk
          rcases h : P k with _ | ⟨x, xs⟩
          · simp [hc', h, List.tail_drop]
          · simp [hc', h]
        · rw [update_of_ne hk, update_of_ne hk, hc']
          split
          · rw [update_of_ne hk]
          · rfl
      have hb : ∀ k, c' k + ops q ≤ d := by
        intro k
        have := hc k
        simp only [ops] at this
        rw [hc']
        split
        · by_cases hk : k = k₀
          · subst hk; simp; omega
          · rw [update_of_ne hk]; omega
        · omega
      simp only [TM2.stepAux, eff]
      rw [← readTop_eq d S0 P c k₀ hk, e]
      exact ih _ _ c' hb
  | load a q ih =>
      intro v P c hc
      simp only [TM2.stepAux, eff]
      exact ih _ P c fun k => by have := hc k; simp only [ops] at this; omega
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c hc
      simp only [TM2.stepAux, eff]
      cases p v
      · simp only [Bool.cond_false]
        exact ih₂ v P c fun k => by have := hc k; simp only [ops] at this; omega
      · simp only [Bool.cond_true]
        exact ih₁ v P c fun k => by have := hc k; simp only [ops] at this; omega
  | goto f => intro v P c _; rfl
  | halt => intro v P c _; rfl

end Agree

/-- **Idle-extended step.** For a finite TM2 machine $M$ and a configuration $c$, the idle-extended
step of $M$ at $c$ is the configuration that one step of $M$ produces from $c$ when the label of
$c$ is not the halted label, and is $c$ itself when it is (a halted configuration stays put). -/
def stepI (M : FinTM2) (c : M.Cfg) : M.Cfg := (TM2.step M.m c).getD c

/-- **Idle-extended run.** For a finite TM2 machine $M$ and a configuration $c$, the idle-extended
run of $M$ from $c$ is the sequence of configurations whose term at time $0$ is $c$ and whose term
at time $t + 1$ is the idle-extended step of $M$ applied to its term at time $t$. -/
def runI (M : FinTM2) (c : M.Cfg) : ℕ → M.Cfg
  | 0 => c
  | t + 1 => stepI M (runI M c t)

/-- **Windows of a configuration.** Let $M$ be a finite TM2 machine with window depth $d$ and let
$c$ be a configuration. The window of $c$ on stack $k$ is the list of length $d$ whose entry at
position $j < d$ is the symbol at depth $j$ of stack $k$ (counted from the top, starting at $0$)
when the stack has more than $j$ symbols, and the empty cell $\bot$ otherwise. -/
def winC (M : FinTM2) (c : M.Cfg) : ∀ k, List (Option (M.Γ k)) :=
  fun k => window (depth M) (c.stk k)

/-- **The idle-extended step is the situation step applied to the stacks.** Let $M$ be a finite
TM2 machine and $c$ a configuration with label $l$, state $v$ and stacks $S$, and let
$(l', v', P, n)$ be the situation step of $M$ at label $l$ and state $v$ on the windows of $c$.
Then the idle-extended step of $M$ at $c$ is the configuration with label $l'$, state $v'$ and,
on each stack $k$, the list $P_k$ placed on top of what remains of $S_k$ after removing its top
$n_k$ symbols.

This is an equality of full configurations and needs no bound on the stack heights. -/
theorem step_agree (M : FinTM2) (c : M.Cfg) :
    stepI M c = applyEff c.stk (sitStep M c.l c.var (winC M c)) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [stepI, TM2.step, sitStep, applyEff]; try rfl
  | some l =>
      simp only [stepI, TM2.step, Option.getD_some, sitStep]
      have := eff_agree (depth M) S (M.m l) v (fun _ => []) (fun _ => 0)
        (fun _ => by simpa using ops_le_depth M l)
      simp only [List.nil_append, List.drop_zero] at this
      exact this

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-! ## [B1] The table-driven step on encoded rows -/

/-- **Label-and-state code of a configuration.** For an encoding $E$ of a machine $M$ and a
configuration $c$ of $M$, this is the number that $E$'s (label, state) numbering assigns to the
pair formed by the label of $c$ (possibly the halted label) and the state of $c$. -/
def code (c : M.Cfg) : ℕ := E.lc (c.l, c.var)

/-- **Cell code of a configuration.** For an encoding $E$ of a machine $M$, a configuration $c$ of
$M$ and natural numbers $k$ and $j$, this is the code under $E$ of the symbol at position $j$
(counting from $0$ at the top) of the stack that $E$'s inverse stack numbering assigns to $k$, in
$c$; it is $0$ (the code of ⊥) if that stack has at most $j$ symbols. -/
def cell (c : M.Cfg) (k j : ℕ) : ℕ := ((c.stk (E.kd k))[j]?).elim 0 (E.enc (E.kd k))

/-- **Situation index of a configuration.** Fix an encoding $E$ of a finite TM2 machine $M$, with
$K$ stacks, symbol-code bound $g$ and window depth $d$. The situation index of a configuration $c$
is the number

$$\sum_{k < K} \sum_{j < d} \mathrm{cell}_c(k, j)\, g^{kd + j} + \mathrm{code}(c)\, g^{Kd},$$

where $\mathrm{code}(c)$ is the combined (label, state) code of $c$ and $\mathrm{cell}_c(k, j)$ is
the cell code of $c$ on stack number $k$ at depth $j$ ($0$ for the empty cell). -/
def sitIdx (c : M.Cfg) : ℕ :=
  mix E.g (E.code c) (E.KK * depth M) fun n => E.cell c (n / depth M) (n % depth M)

/-- **The table-driven row update.** Fix an encoding $E$ of a finite TM2 machine, a row height $H$,
a situation $i$ and an old row $\mathrm{old}$ giving a code for each stack number $k$ and depth
$j$. For a stack number $k$, write $p$ for the number of symbols situation $i$ leaves pushed on
stack $k$ and $n$ for the number of original symbols it consumes from stack $k$. The updated row
at $(k, j)$ is the code of the symbol situation $i$ leaves at depth $j$ of stack $k$ if $j < p$;
otherwise it is $\mathrm{old}(k, j - p + n)$ if $j < (H \mathbin{\dot{-}} \max(p, n)) + p$, where
$\dot{-}$ is truncated subtraction; otherwise it is $0$, the empty cell.

These are the three cases the shift clauses force: pushed fill, in-range shift and overflow. -/
def tabRow (H i : ℕ) (old : ℕ → ℕ → ℕ) (k j : ℕ) : ℕ :=
  if j < E.pl i k then E.pu i k j
  else if j < H - max (E.pl i k) (E.cn i k) + E.pl i k then old k (j - E.pl i k + E.cn i k)
  else 0

/-- **Good configurations.** For an encoding $E$ of a machine $M$, a configuration $c$ of $M$ is
good when every symbol on every stack $k$ of $c$ is one of the effective symbols of stack $k$
listed by $E$ (so that it has a code). -/
def Good (c : M.Cfg) : Prop := ∀ k, ∀ x ∈ c.stk k, ∃ n, E.dec k n = x

theorem cell_kc (c : M.Cfg) (k : M.K) (j : ℕ) :
    E.cell c (E.kc k) j = ((c.stk k)[j]?).elim 0 (E.enc k) := by
  unfold cell; rw [E.kd_kc]

theorem decO_zero (k : M.K) : E.decO k 0 = none := by
  unfold decO; rw [dite_eq_right (by omega)]

theorem decO_cell (c : M.Cfg) (hc : E.Good c) (k : M.K) (j : ℕ) :
    E.decO k (((c.stk k)[j]?).elim 0 (E.enc k)) = (c.stk k)[j]? := by
  rcases h : (c.stk k)[j]? with _ | x
  · exact E.decO_zero k
  · obtain ⟨n, rfl⟩ := hc k x (List.mem_of_getElem? h)
    simp only [Option.elim_some, E.enc_dec]
    exact E.decO_succ k n

theorem cell_lt (c : M.Cfg) (hc : E.Good c) (k j : ℕ) : E.cell c k j < E.g := by
  unfold cell
  rcases h : (c.stk (E.kd k))[j]? with _ | x
  · exact E.g_pos
  · obtain ⟨n, rfl⟩ := hc _ x (List.mem_of_getElem? h)
    simp only [Option.elim_some, E.enc_dec]
    have := n.2; have := E.sz_lt_g (E.kd k); omega

/-- **The situation index matches the code and windows.** Fix an encoding $E$ of a finite TM2
machine $M$, with $K$ stacks, $N$ situations and window depth $d$. If every symbol on every stack
of a configuration $c$ lies in the effective alphabet of $E$, then the situation index $i$ of $c$
satisfies $i < N$, the label/state code of situation $i$ equals the combined (label, state) code
of $c$, and for all $k < K$ and $j < d$ the window symbol code of situation $i$ on stack $k$ at
depth $j$ equals the cell code of $c$ on stack number $k$ at depth $j$. -/
theorem sitIdx_spec (c : M.Cfg) (hc : E.Good c) :
    E.sitIdx c < E.N ∧ E.la (E.sitIdx c) = E.code c ∧
      ∀ k < E.KK, ∀ j < depth M, E.wa (E.sitIdx c) k j = E.cell c k j :=
  E.mix_sit _ (E.lc_lt _) _ fun k _ j _ => E.cell_lt c hc k j

theorem win_sitIdx (c : M.Cfg) (hc : E.Good c) : E.win (E.sitIdx c) = winC M c := by
  funext k
  unfold win winC window
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [(E.sitIdx_spec c hc).2.2 _ (E.kc_lt k) j hj, E.cell_kc, E.decO_cell c hc]

theorem res_sitIdx (c : M.Cfg) (hc : E.Good c) :
    E.res (E.sitIdx c) = sitStep M c.l c.var (winC M c) := by
  unfold res
  rw [(E.sitIdx_spec c hc).2.1, code, E.ld_lc, E.win_sitIdx c hc]

/-- **Cells of a pushed prefix over a truncated stack.** Let $e$ map elements of $\alpha$ to natural
numbers, and for a list $L$ over $\alpha$ and $i \in \mathbb{N}$ let $L\langle i\rangle$ be $e$ of
the entry of $L$ at position $i$ (counting from $0$), or $0$ if $L$ has at most $i$ entries.
Subtraction of natural numbers is truncated at $0$. Let $P$ and $S$ be lists over $\alpha$ and
$n, H, d, j \in \mathbb{N}$ with $|P| \le d$, $n \le d$ and $|S| \le H - d$, and let $Q$ be $P$
followed by $S$ with its first $n$ entries removed. If $j < |P|$ then
$Q\langle j\rangle = P\langle j\rangle$; otherwise, if $j < (H - \max(|P|, n)) + |P|$ then
$Q\langle j\rangle = S\langle j - |P| + n\rangle$; and otherwise $Q\langle j\rangle = 0$. -/
theorem row_cell {α : Type} (e : α → ℕ) (P S : List α) (n H d j : ℕ) (hP : P.length ≤ d)
    (hn : n ≤ d) (hS : S.length ≤ H - d) :
    ((P ++ S.drop n)[j]?).elim 0 e =
      if j < P.length then (P[j]?).elim 0 e
      else if j < H - max P.length n + P.length then (S[j - P.length + n]?).elim 0 e
      else 0 := by
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, Nat.add_comm]
  · have hm : max P.length n ≤ d := max_le hP hn
    rw [List.getElem?_eq_none]
    · rfl
    · simp only [List.length_append, List.length_drop]; omega

/-- **The table-driven step.** Fix an encoding $E$ of a finite TM2 machine $M$, with $K$ stacks
and window depth $d$, and a natural number $H$. Let $c$ be a configuration such that every symbol
on every stack of $c$ lies in the effective alphabet of $E$ and every stack of $c$ has length at
most $H \mathbin{\dot{-}} d$ (truncated subtraction). Let $c'$ be the idle-extended step of $M$ at
$c$ and $i$ the situation index of $c$. Then the combined (label, state) code of $c'$ is the next
label/state code after situation $i$, and for all $k < K$ and $j < H$ the cell code of $c'$ on
stack number $k$ at depth $j$ is the value at $(k, j)$ of the table-driven row update with height
$H$ and situation $i$ applied to the cell codes of $c$.

No hypothesis $d \le H$ is needed: if $H < d$, every stack of $c$ is empty. -/
theorem table_agree (H : ℕ) (c : M.Cfg) (hc : E.Good c)
    (hh : ∀ k, (c.stk k).length ≤ H - depth M) :
    E.code (stepI M c) = E.na (E.sitIdx c) ∧
      ∀ k < E.KK, ∀ j < H, E.cell (stepI M c) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j := by
  have hr := E.res_sitIdx c hc
  have hs := step_agree M c
  refine ⟨?_, fun k _ j _ => ?_⟩
  · rw [hs]; simp only [code, na, hr]; try rfl
  · have hpl := E.pl_le (E.sitIdx c) k
    have hcn := E.cn_le (E.sitIdx c) k
    unfold pl at hpl; unfold cn at hcn
    rw [hr] at hpl hcn
    unfold tabRow pl cn pu cell
    rw [hr, hs]
    exact row_cell _ _ _ _ H (depth M) j hpl hcn (hh _)

/-- **Reads of the in-range shift stay in the row.** Fix an encoding $E$ of a finite TM2 machine
and natural numbers $H$, $i$, $k$ and $j$. Write $p$ for the number of symbols situation $i$
leaves pushed on stack number $k$ and $n$ for the number of original symbols it consumes from
stack number $k$. If $p \le j$ and $j < (H \mathbin{\dot{-}} \max(p, n)) + p$, where $\dot{-}$ is
truncated subtraction, then $j - p + n < H$.

So every old cell that the table-driven row update reads lies in the row of height $H$. -/
theorem tabRow_reads_lt (H i k j : ℕ) (hpl : E.pl i k ≤ j)
    (hj : j < H - max (E.pl i k) (E.cn i k) + E.pl i k) :
    j - E.pl i k + E.cn i k < H := by omega

/-! ## [B2] Every configuration of a real run is good (`run_mem_Γfin`) -/

/-- **The idle-extended step preserves good configurations.** Let $E$ be an encoding of a finite
TM2 machine $M$ and let $c$ be a configuration of $M$. If $c$ is good for $E$, then so is the
idle-extended step of $M$ at $c$. -/
theorem good_step (c : M.Cfg) (hc : E.Good c) : E.Good (stepI M c) := by
  rw [step_agree]
  intro k x hx
  simp only [applyEff, List.mem_append] at hx
  rcases hx with hx | hx
  · unfold sitStep at hx
    split at hx
    · simp at hx
    · next l _ =>
      exact eff_pushed (winC M c) (fun k x => ∃ n, E.dec k n = x) (M.m l)
        (fun k x h => E.push_mem l k x h) _ _ _ (fun _ _ h => by simp at h) k x hx
  · exact hc k x (List.mem_of_mem_drop hx)

theorem good_init (s : List (M.Γ M.k₀)) : E.Good (initList M s) := by
  intro k x hx
  by_cases hk : k = M.k₀
  · subst hk
    simp only [initList, dite_eq_left] at hx
    exact E.input_mem x
  · simp [initList, hk] at hx

theorem run_good (s : List (M.Γ M.k₀)) : ∀ t, E.Good (runI M (initList M s) t)
  | 0 => E.good_init s
  | t + 1 => E.good_step _ (run_good s t)

/-- **The table-driven step along a run.** Fix an encoding $E$ of a finite TM2 machine $M$, with
$K$ stacks, $N$ situations and window depth $d$, a natural number $H$, an input list $s$ and a
time $t$. For each time $u$ let $c_u$ be the configuration at time $u$ of the idle-extended run
of $M$ from the initial configuration of $M$ on input $s$, and let $i$ be the situation index of
$c_t$. If every stack of $c_t$ has length at most $H \mathbin{\dot{-}} d$ (truncated subtraction),
then $i < N$; the label/state code of situation $i$ is the combined (label, state) code of $c_t$;
for all $k < K$ and $j < d$ the window symbol code of situation $i$ on stack $k$ at depth $j$ is
the cell code of $c_t$ on stack number $k$ at depth $j$; the combined (label, state) code of
$c_{t+1}$ is the next label/state code after situation $i$; and for all $k < K$ and $j < H$ the
cell code of $c_{t+1}$ on stack number $k$ at depth $j$ is the value at $(k, j)$ of the
table-driven row update with height $H$ and situation $i$ applied to the cell codes of $c_t$.

Unlike the single-step version, no alphabet hypothesis is needed: every symbol on a stack of such
a run lies in the effective alphabet of $E$. -/
theorem table_agree_run (H : ℕ) (s : List (M.Γ M.k₀)) (t : ℕ)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    let c := runI M (initList M s) t
    E.sitIdx c < E.N ∧ E.la (E.sitIdx c) = E.code c ∧
      (∀ k < E.KK, ∀ j < depth M, E.wa (E.sitIdx c) k j = E.cell c k j) ∧
      E.code (runI M (initList M s) (t + 1)) = E.na (E.sitIdx c) ∧
      ∀ k < E.KK, ∀ j < H,
        E.cell (runI M (initList M s) (t + 1)) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j :=
  ⟨(E.sitIdx_spec _ (E.run_good s t)).1, (E.sitIdx_spec _ (E.run_good s t)).2.1,
    (E.sitIdx_spec _ (E.run_good s t)).2.2, E.table_agree H _ (E.run_good s t) hh⟩

end Enc

/-! ## [C1] Decoding a row of cells (generic part) -/

section DecS

variable {α : Type}

/-- **Reading a list from a sequence of cells.** For $f$ mapping each natural number to an element
of $\alpha$ or to ⊥, and $j, m \in \mathbb{N}$, this is the list $[x_0, \dots, x_{r-1}]$ with
$f(j + i) = x_i$ for each $i < r$, where $r = m$ if none of $f(j), \dots, f(j + m - 1)$ is ⊥, and
otherwise $r$ is the least $i < m$ with $f(j + i) = \bot$. -/
def decS (f : ℕ → Option α) : ℕ → ℕ → List α
  | _, 0 => []
  | j, m + 1 => match f j with
    | none => []
    | some x => x :: decS f (j + 1) m

theorem decS_length (f : ℕ → Option α) : ∀ j m, (decS f j m).length ≤ m
  | _, 0 => by simp [decS]
  | j, m + 1 => by
    unfold decS
    split
    · simp
    · have := decS_length f (j + 1) m; simp; omega

theorem mem_decS (f : ℕ → Option α) (x : α) : ∀ j m, x ∈ decS f j m → ∃ i, f i = some x
  | _, 0, h => by simp [decS] at h
  | j, m + 1, h => by
    unfold decS at h
    split at h
    · simp at h
    · next y hy =>
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨j, hy⟩
      · exact mem_decS f x (j + 1) m h

theorem decS_congr (f f' : ℕ → Option α) : ∀ j m, (∀ i < m, f (j + i) = f' (j + i)) →
    decS f j m = decS f' j m
  | _, 0, _ => rfl
  | j, m + 1, h => by
    have h0 : f j = f' j := by simpa using h 0 (by omega)
    have ih := decS_congr f f' (j + 1) m fun i hi => by
      have := h (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this
    simp only [decS, h0, ih]

/-- **Reading back a list from its cells.** Let $f$ map each natural number to an element of
$\alpha$ or to ⊥, let $S$ be a list over $\alpha$, and let $j, m \in \mathbb{N}$. Suppose that for
every $i \in \mathbb{N}$, $f(j + i)$ is the entry of $S$ at position $i$ (counting from $0$) when
$i$ is less than the length of $S$, and ⊥ otherwise. If $S$ has length at most $m$, then reading
$f$ from position $j$ for at most $m$ positions, stopping at the first ⊥, gives $S$. -/
theorem decS_of_list (f : ℕ → Option α) : ∀ (S : List α) (j m : ℕ),
    (∀ i, f (j + i) = S[i]?) → S.length ≤ m → decS f j m = S
  | [], j, 0, _, _ => rfl
  | [], j, m + 1, h, _ => by have := h 0; simp at this; simp [decS, this]
  | x :: S, j, 0, _, hl => by simp at hl
  | x :: S, j, m + 1, h, hl => by
    have h0 : f j = some x := by simpa using h 0
    have ih := decS_of_list f S (j + 1) m (fun i => by
      have := h (i + 1); rwa [show j + (i + 1) = j + 1 + i by omega] at this)
      (by simp at hl; omega)
    simp only [decS, h0, ih]

/-- **Entries of a decoded stack on prefix-form input.** Let $f : \mathbb{N} \to
\mathrm{Option}\,\alpha$ and write $\bot$ for the absent value. For $j, m \in \mathbb{N}$ let
$\mathrm{decS}(f, j, m)$ be the list of the values $f(j), f(j + 1), \dots$, read for at most $m$
positions and stopped at the first $\bot$. Suppose $f$ is in prefix form on the window from $j$
to $j + m$: whenever $j \le a \le b < j + m$ and $f(a) = \bot$, also $f(b) = \bot$. Then for every
$i < m$, the $i$-th entry of $\mathrm{decS}(f, j, m)$, taken to be $\bot$ when the list has at
most $i$ entries, equals $f(j + i)$. -/
theorem getElem?_decS (f : ℕ → Option α) : ∀ (j m : ℕ),
    (∀ a b, j ≤ a → a ≤ b → b < j + m → f a = none → f b = none) →
    ∀ i < m, (decS f j m)[i]? = f (j + i)
  | _, 0, _, i, hi => by omega
  | j, m + 1, hp, i, hi => by
    unfold decS
    split
    · next hn =>
      exact (hp j (j + i) le_rfl (by omega) (by omega) hn).symm ▸ (by simp)
    · next x hx =>
      rcases i with _ | i
      · simpa using hx.symm
      · have := getElem?_decS f (j + 1) m
          (fun a b ha hab hb => hp a b (by omega) hab (by omega)) i (by omega)
        simp only [List.getElem?_cons_succ, this]
        congr 1; omega

end DecS

/-- **Stack heights grow by at most the window depth per step.** Let $M$ be a finite multi-stack
Turing machine (finitely many stacks, labels and states, and a finite input alphabet), and let $d$
be its window depth, the largest number of push, peek and pop nodes on a root-to-leaf path of any
of its statement trees. For every configuration $c$ of $M$ and every stack $k$, the length of
stack $k$ after one idle-extended step of $M$ from $c$ is at most the length of stack $k$ of $c$
plus $d$. -/
theorem stepI_height {M : FinTM2} (c : M.Cfg) (k : M.K) :
    ((stepI M c).stk k).length ≤ (c.stk k).length + depth M := by
  rw [step_agree]
  simp only [applyEff, List.length_append, List.length_drop]
  have : ((sitStep M c.l c.var (winC M c)).2.2.1 k).length ≤ depth M := by
    unfold sitStep
    split
    · simp
    · next l _ =>
      have := eff_bound (winC M c) (M.m l) c.var (fun _ => []) (fun _ => 0) k
      have := ops_le_depth M l
      simp only [List.length_nil] at *; omega
  omega

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **C1 decoder (decoding a row).** Let $E$ be an encoding of a machine $M$, let
$H, n \in \mathbb{N}$, and let $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. The decoded
configuration has the label and the state that the inverse (label, state) numbering of $E$
assigns to $n$. For each stack $k$ of $M$, with stack number $\kappa$, the decoded stack $k$
lists, from the top, the symbols of stack $k$ with codes $w(\kappa, 0), w(\kappa, 1), \dots$,
stopping before the first $j$ at which $w(\kappa, j)$ is $0$ or is not a valid code of stack
$k$, and taking at most $H$ symbols. The valid codes of stack $k$ are $1, \dots, s$, where $s$ is
the size of its effective alphabet, and code $i + 1$ stands for symbol number $i$ of that
alphabet, counting from $0$. -/
def decRow (H n : ℕ) (w : ℕ → ℕ → ℕ) : M.Cfg :=
  ⟨(E.ld n).1, (E.ld n).2, fun k => decS (fun j => E.decO k (w (E.kc k) j)) 0 H⟩

/-- **Well-formed rows of cells.** Let $M$ be a finite multi-stack Turing machine and $E$ an
encoding of $M$ with $K$ numbered stacks, let $H \in \mathbb{N}$, and let
$w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ assign a code $w(k, j)$ to each stack number $k$
and depth $j$. The row $w$ is well formed at height $H$ when for every $k < K$ and every $j < H$:
$w(k, j)$ is at most the size of the effective alphabet of the stack numbered $k$, and if
$w(k, j) = 0$ then $w(k, b) = 0$ for every $b$ with $j \le b < H$.

Code $0$ is the empty cell, so the second condition says that each stack is in prefix form. -/
def RowOK (H : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, w k j ≤ E.sz (E.kd k) ∧ (w k j = 0 → ∀ b, j ≤ b → b < H → w k b = 0)

theorem decO_eq_none (k : M.K) (n : ℕ) (hn : n ≤ E.sz k) (h : E.decO k n = none) : n = 0 := by
  unfold decO at h
  split at h
  · simp at h
  · next h' => omega

theorem enc_decO (k : M.K) (n : ℕ) (hn : n ≤ E.sz k) : (E.decO k n).elim 0 (E.enc k) = n := by
  unfold decO
  split
  · next h => simp only [Option.elim_some, E.enc_dec]; omega
  · next h => simp only [Option.elim_none]; omega

/-- **C1a (decoding recovers a good configuration).** Let $E$ be an encoding of a machine $M$,
let $H \in \mathbb{N}$, and let $c$ be a good configuration of $M$ (every symbol on every stack
of $c$ lies in the effective alphabet of $E$) all of whose stacks have length at most $H$. Then
the row decoder of $E$ at height $H$, applied to the (label, state) code of $c$ and the cell
array of $c$, returns $c$. -/
theorem decRow_enc (H : ℕ) (c : M.Cfg) (hc : E.Good c) (hh : ∀ k, (c.stk k).length ≤ H) :
    E.decRow H (E.code c) (E.cell c) = c := by
  obtain ⟨l, v, S⟩ := c
  simp only [decRow, code, E.ld_lc]
  congr 1
  funext k
  refine decS_of_list _ _ 0 H (fun i => ?_) (hh k)
  rw [Nat.zero_add]
  first | exact (congrArg (E.decO k) (E.cell_kc ⟨l, v,
      S⟩ k i)).trans (E.decO_cell _ hc k i) | (erw [E.cell_kc]; exact E.decO_cell _ hc k i)

/-- **C1b (decoding a well-formed row loses nothing).** Let $E$ be an encoding of a machine $M$
with $K$ numbered stacks and $A_0$ (label, state) codes, let $H \in \mathbb{N}$, let $n < A_0$,
and let $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be a well-formed row of height $H$: for
all $k < K$ and $j < H$, $w(k, j)$ is at most the size of the effective alphabet of stack number
$k$, and if $w(k, j) = 0$ then $w(k, b) = 0$ for every $b$ with $j \le b < H$. Let $c$ be the
configuration that the row decoder of $E$ at height $H$ returns on code $n$ and array $w$. Then
the (label, state) code of $c$ is $n$, and the cell code of $c$ at stack number $k$ and depth $j$
equals $w(k, j)$ for all $k < K$ and $j < H$. -/
theorem enc_decRow (H n : ℕ) (hn : n < E.A0) (w : ℕ → ℕ → ℕ) (hw : E.RowOK H w) :
    E.code (E.decRow H n w) = n ∧ ∀ k < E.KK, ∀ j < H, E.cell (E.decRow H n w) k j = w k j := by
  refine ⟨by simp only [code, decRow, E.lc_ld n hn], fun k hk j hj => ?_⟩
  simp only [cell, decRow]
  rw [getElem?_decS _ 0 H ?_ j hj, Nat.zero_add, E.kc_kd k hk]
  · exact E.enc_decO _ _ (hw k hk j hj).1
  · intro a b _ hab hb ha
    rw [E.kc_kd k hk] at ha ⊢
    have := E.decO_eq_none _ _ (hw k hk a (by omega)).1 ha
    rw [(hw k hk a (by omega)).2 this b hab (by omega)]
    exact E.decO_zero _

/-- **C1c (cell arrays of good configurations are well-formed rows).** Let $E$ be an encoding
of a machine $M$ with $K$ numbered stacks, and let $c$ be a good configuration of $M$, that is,
every symbol on every stack of $c$ lies in the effective alphabet of $E$. Let $w$ be the cell
array of $c$: $w(k, j)$ is the code of the symbol at depth $j$ from the top of stack number $k$,
or $0$ if there is none. Then for every $H \in \mathbb{N}$, $w$ is a well-formed row of height
$H$: for all $k < K$ and $j < H$, the code $w(k, j)$ is at most the size of the effective
alphabet of stack number $k$, and if $w(k, j) = 0$ then $w(k, b) = 0$ for every $b$ with
$j \le b < H$. -/
theorem cell_rowOK (H : ℕ) (c : M.Cfg) (hc : E.Good c) : E.RowOK H (E.cell c) := by
  intro k _ j _
  have key : ∀ j, (E.cell c k j = 0 ∧ (c.stk (E.kd k)).length ≤ j) ∨
      (j < (c.stk (E.kd k)).length ∧ 1 ≤ E.cell c k j ∧ E.cell c k j ≤ E.sz (E.kd k)) := by
    intro j
    unfold cell
    rcases h : (c.stk (E.kd k))[j]? with _ | x
    · exact Or.inl ⟨rfl, List.getElem?_eq_none_iff.1 h⟩
    · obtain ⟨m, rfl⟩ := hc _ x (List.mem_of_getElem? h)
      refine Or.inr ⟨(List.getElem?_eq_some_iff.1 h).1, ?_⟩
      simp only [Option.elim_some, E.enc_dec]; have := m.2; omega
  refine ⟨by rcases key j with h | h <;> omega, fun h0 b hjb _ => ?_⟩
  have hlen : (c.stk (E.kd k)).length ≤ j := by rcases key j with h | h <;> omega
  unfold cell
  rw [List.getElem?_eq_none (by omega)]; rfl

/-- **C1d (decoded configurations are good).** Let $E$ be an encoding of a machine $M$. For all
$H, n \in \mathbb{N}$ and every $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$, the configuration
that the row decoder of $E$ at height $H$ returns on code $n$ and array $w$ is good: every symbol
on each of its stacks lies in the effective alphabet of $E$. -/
theorem decRow_good (H n : ℕ) (w : ℕ → ℕ → ℕ) : E.Good (E.decRow H n w) := by
  intro k x hx
  obtain ⟨i, hi⟩ := mem_decS _ x 0 H hx
  unfold decO at hi
  split at hi
  · exact ⟨_, Option.some_inj.1 hi⟩
  · simp at hi

theorem decRow_height (H n : ℕ) (w : ℕ → ℕ → ℕ) (k : M.K) : ((E.decRow H n w).stk k).length ≤ H :=
  decS_length _ 0 H

/-- **C1e (the row decoder reads only the window).** Let $E$ be an encoding of a machine $M$
with $K$ numbered stacks, let $H, n \in \mathbb{N}$, and let
$w, w' : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. If $w(k, j) = w'(k, j)$ for all $k < K$ and
$j < H$, then the row decoder of $E$ at height $H$ returns the same configuration on code $n$
and array $w$ as on code $n$ and array $w'$. -/
theorem decRow_congr (H n : ℕ) (w w' : ℕ → ℕ → ℕ) (h : ∀ k < E.KK, ∀ j < H, w k j = w' k j) :
    E.decRow H n w = E.decRow H n w' := by
  simp only [decRow]
  congr 1
  funext k
  exact decS_congr _ _ 0 H fun i hi => by rw [h _ (E.kc_lt k) _ (by omega)]

/-- **Good configurations are determined by their row (C1f).** Let $M$ be a finite multi-stack
Turing machine and $E$ an encoding of $M$ with $K$ numbered stacks, let $H \in \mathbb{N}$, and
for a configuration $c$ write $\mathrm{cell}(c, k, j)$ for the code of the symbol at depth $j$ of
the stack numbered $k$ ($0$ if there is none). Let $c$ and $c'$ be configurations that are good
for $E$ (every stack symbol lies in the effective alphabet of its stack) and all of whose stacks
have length at most $H$. If $c$ and $c'$ have the same (label, state) code and
$\mathrm{cell}(c, k, j) = \mathrm{cell}(c', k, j)$ for all $k < K$ and $j < H$, then $c = c'$. -/
theorem row_inj (H : ℕ) (c c' : M.Cfg) (hc : E.Good c) (hc' : E.Good c')
    (hh : ∀ k, (c.stk k).length ≤ H) (hh' : ∀ k, (c'.stk k).length ≤ H)
    (hcode : E.code c = E.code c') (hcell : ∀ k < E.KK, ∀ j < H, E.cell c k j = E.cell c' k j) :
    c = c' := by
  rw [← E.decRow_enc H c hc hh, ← E.decRow_enc H c' hc' hh', hcode, E.decRow_congr H _ _ _ hcell]

/-- **C2' (decoding the table-driven row gives the next configuration).** Let $E$ be an encoding
of a machine $M$ with window depth $d$, let $H \ge d$ be a natural number, and let $c$ be a good
configuration of $M$ (every symbol on every stack of $c$ lies in the effective alphabet of $E$)
all of whose stacks have length at most $H - d$. Let $i$ be the situation index of $c$. Then the
row decoder of $E$ at height $H$, applied to the next (label, state) code of situation $i$ and to
the table-driven row update at height $H$ of situation $i$ on the cell array of $c$, returns the
idle-extended step of $c$: the configuration after one step of $M$, or $c$ itself if $c$ is
halted. -/
theorem decRow_tabRow (H : ℕ) (hH : depth M ≤ H) (c : M.Cfg) (hc : E.Good c)
    (hh : ∀ k, (c.stk k).length ≤ H - depth M) :
    E.decRow H (E.na (E.sitIdx c)) (E.tabRow H (E.sitIdx c) (E.cell c)) = stepI M c := by
  obtain ⟨h1, h2⟩ := E.table_agree H c hc hh
  rw [← h1, E.decRow_congr H _ _ (E.cell (stepI M c)) fun k hk j hj => (h2 k hk j hj).symm]
  exact E.decRow_enc H _ (E.good_step c hc) fun k => by
    have := stepI_height c k; have := hh k; omega

end Enc

/-! ## [C6] Clause forcing: the in-range shift family (no row decoding) -/

section C6

open Cslib.Complexity.DenseSAT

/-- **Truth of a variable under an assignment.** For an assignment $a$, given as a list of
booleans, and a variable index $v \in \mathbb{N}$, the variable $v$ is true under $a$ when $v$ is
less than the length of $a$ and the entry of $a$ at position $v$ is true. In particular, variables
with index at least the length of $a$ are not true. -/
def Tr (a : List Bool) (v : ℕ) : Prop := a[v]? = some true

theorem mem_of_lookup {p : ℕ} {b : Bool} :
    ∀ {ls : List (ℕ × Bool)}, ls.lookup p = some b → (p, b) ∈ ls
  | [], h => by simp at h
  | (q, c) :: r, h => by
    by_cases hq : p = q
    · subst hq
      simp at h
      simp [h]
    · rw [Family.lookup_cons_ne hq] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- **L0 (a satisfied dense clause has a satisfied listed literal).** Let $V \in \mathbb{N}$, let
$\ell$ be a list of pairs $(p, b)$ of a variable index $p \in \mathbb{N}$ and a sign $b$ (true or
false), and let $a$ be a list of booleans. If $a$ satisfies the dense clause over $V$ variables
built from $\ell$, then some pair $(p, b) \in \ell$ has $p$ less than the length of $a$ and
$a_p = b$. -/
theorem clauseSat_dense {V : ℕ} {ls : List (ℕ × Bool)} {a : List Bool}
    (h : clauseSat (Family.denseClause V ls) a) : ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b := by
  obtain ⟨j, b, hc, ha⟩ := h
  unfold Family.denseClause at hc
  have hj : j < V := by
    by_contra hj
    rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)] at hc
    simp at hc
  rw [List.getElem?_map, List.getElem?_range hj] at hc
  simp only [Option.map_some, Option.some.injEq] at hc
  exact ⟨j, b, mem_of_lookup hc, ha⟩

/-- **In-range shift forcing (L1).** Let $L$ be a layout with $K$ stacks and $g$ symbol codes,
let $sa$, $pl$, $cn$, $pu$ be situation tables and $N, T, H \in \mathbb{N}$, and let $a$ be an
assignment satisfying the cell-shift clause family of $L$ with these tables and bounds $N$, $T$,
$H$. Call a variable true when its index is less than the length of $a$ and $a$ is true there.
Write $S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$ and $C[t, k, j, x]$ for the
cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$). Let
$t < T$, $i < N$, $k < K$, $x < g$ and $u < H - \max(pl(i, k), cn(i, k))$, with truncated
subtraction. If $S[t, i]$ and $C[t, k, u + cn(i, k), x]$ are true, then
$C[t + 1, k, u + pl(i, k), x]$ is true. -/
theorem sh_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k u x : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK)
    (hu : u < H - max (pl i k) (cn i k)) (hx : x < L.g)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) (hC : Tr a (L.cIdx H t k (u + cn i k) x)) :
    Tr a (L.cIdx H (t + 1) k (u + pl i k) x) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.shLits L sa pl cn H t i k u x) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u,
        List.mem_range.2 hu,
      List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩⟩))
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.shLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS hC ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hC] at hab; simp at hab
  · rw [hS] at hab; simp at hab
  · exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Cell block of a row equal to an array.** Let $E$ be an encoding of a machine $M$ with $K$
numbered stacks and $g$ symbol codes, let $a$ be a list of booleans, let $H, t \in \mathbb{N}$,
and let $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. The cell block of row $t$ is exactly
$w$ under $a$ when, for all $k < K$, $j < H$ and $x < g$, the cell variable for time $t$,
stack $k$, depth $j$ and symbol code $x$ in the layout of $E$ at height $H$ is true under $a$ if
and only if $x = w(k, j)$. A variable $v$ is true under $a$ when $v$ is less than the length of
$a$ and the entry of $a$ at position $v$ is true. -/
def CellsAre (a : List Bool) (H t : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, ∀ x < E.g, Tr a (E.layout.cIdx H t k j x) ↔ x = w k j

/-- **Cell literals of an array hold in a row.** Let $E$ be an encoding of a machine $M$ with
$K$ numbered stacks, let $a$ be a list of booleans, let $H, t \in \mathbb{N}$, and let
$w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. The cell literals of $w$ hold in row $t$ under
$a$ when, for all $k < K$ and $j < H$, the cell variable for time $t$, stack $k$, depth $j$ and
symbol code $w(k, j)$ in the layout of $E$ at height $H$ is true under $a$, that is, its index is
less than the length of $a$ and the entry of $a$ at that index is true.

Unlike the exact form, this says nothing about the cell variables for other symbol codes. -/
def CellsHold (a : List Bool) (H t : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, Tr a (E.layout.cIdx H t k j (w k j))

/-- **Positive core of the shift step (L2⁺).** Let $M$ be a finite multi-stack Turing machine and
$E$ an encoding of $M$ with $K$ numbered stacks, tables $sa$, $pl$, $cn$, $pu$ and $N$ situations,
let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment satisfying the cell-shift
clause family of the layout of $E$ with these tables and bounds $N$, $T$, $H$. Call a variable
true when its index is less than the length of $a$ and $a$ is true there. Write $S[t, i]$ for the
label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for the cell variable of row $t$,
stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and $\mathrm{cell}(c, k, j)$ for
the code at depth $j$ of the stack numbered $k$ of a configuration $c$ ($0$ if there is none).
Let $c$ be a configuration that is good for $E$ (every stack symbol lies in the effective
alphabet of its stack), with situation index $i$. Suppose that
$C[t, k', j', \mathrm{cell}(c, k', j')]$ is true for all $k' < K$ and $j' < H$, and that
$S[t, i]$ is true. Then for every $k < K$ and every $j$ with
$pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$ (truncated subtraction), the variable
$C[t + 1, k, j, R(k, j)]$ is true, where $R$ is the table-driven row update at height $H$ of the
cells of $c$ for situation $i$. -/
theorem sh_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hrow : E.CellsHold a H t (E.cell c))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j =
      E.cell c k (j - E.pl (E.sitIdx c) k + E.cn (E.sitIdx c) k) := by
    unfold tabRow; rw [ite_eq_right (by omega), ite_eq_left hj2]
  have hu : j - E.pl (E.sitIdx c) k < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) := by
    omega
  have := sh_force ha ht (E.sitIdx_spec c hc).1 hk hu (E.cell_lt c hc k _) hS
    (hrow k hk _ (by omega))
  rwa [Nat.sub_add_cancel hj1, ← htab] at this

/-- **Exact shift step (L2).** Let $M$ be a finite multi-stack Turing machine and $E$ an encoding
of $M$ with $K$ numbered stacks, $g$ symbol codes, tables $sa$, $pl$, $cn$, $pu$ and $N$
situations, let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment satisfying
the cell-shift clause family of the layout of $E$ with these tables and bounds $N$, $T$, $H$.
Call a variable true when its index is less than the length of $a$ and $a$ is true there. Write
$S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for the cell
variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and
$\mathrm{cell}(c, k, j)$ for the code at depth $j$ of the stack numbered $k$ of a configuration
$c$ ($0$ if there is none). Let $c$ be a configuration that is good for $E$ (every stack symbol
lies in the effective alphabet of its stack), with situation index $i$. Suppose that for all
$k' < K$, $j' < H$ and $x < g$ the variable $C[t, k', j', x]$ is true exactly when
$x = \mathrm{cell}(c, k', j')$, and that $S[t, i]$ is true. Let $k < K$ and
$pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$ (truncated subtraction), and suppose
at most one $x < g$ makes $C[t + 1, k, j, x]$ true. Then for every $x < g$, $C[t + 1, k, j, x]$
is true exactly when $x = R(k, j)$, where $R$ is the table-driven row update at height $H$ of the
cells of $c$ for situation $i$. -/
theorem sh_step_cell {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hrow : E.CellsAre a H t (E.cell c))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k)
    (hamo : ∀ x < E.g, ∀ y < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) →
      Tr a (E.layout.cIdx H (t + 1) k j y) → x = y) :
    ∀ x < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) ↔
      x = E.tabRow H (E.sitIdx c) (E.cell c) k j := by
  have hon := E.sh_hold ha ht c hc
    (fun k hk j hj => (hrow k hk j hj _ (E.cell_lt c hc k j)).2 rfl) hS hk hj1 hj2
  have hw : E.tabRow H (E.sitIdx c) (E.cell c) k j < E.g := by
    unfold tabRow; rw [ite_eq_right (by omega), ite_eq_left hj2]; exact E.cell_lt c hc _ _
  intro x hx
  exact ⟨fun h => hamo x hx _ hw h hon, fun h => h ▸ hon⟩

/-- **Exact shift step on a real run (L3).** Let $M$ be a finite multi-stack Turing machine and
$E$ an encoding of $M$ with $K$ numbered stacks, $g$ symbol codes, tables $sa$, $pl$, $cn$, $pu$
and $N$ situations, let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment
satisfying the cell-shift clause family of the layout of $E$ with these tables and bounds $N$,
$T$, $H$. Call a variable true when its index is less than the length of $a$ and $a$ is true
there. Write $S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for
the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and
$\mathrm{cell}(c, k, j)$ for the code at depth $j$ of the stack numbered $k$ of a configuration
$c$ ($0$ if there is none). Fix an input list $s$, let $c_n$ be the configuration after $n$
idle-extended steps of $M$ from the initial configuration on $s$, and let $i$ be the situation
index of $c_t$. Suppose that every stack of $c_t$ has length at most $H - d$, where $d$ is the
window depth of $M$, that for all $k' < K$, $j' < H$ and $x < g$ the variable $C[t, k', j', x]$
is true exactly when $x = \mathrm{cell}(c_t, k', j')$, and that $S[t, i]$ is true. Let $k < K$
and $pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$, and suppose at most one $x < g$
makes $C[t + 1, k, j, x]$ true. Then for every $x < g$, $C[t + 1, k, j, x]$ is true exactly when
$x = \mathrm{cell}(c_{t+1}, k, j)$. Subtraction is truncated at $0$.

No row is decoded in the proof. -/
theorem sh_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hrow : E.CellsAre a H t (E.cell (runI M (initList M s) t)))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k)
    (hamo : ∀ x < E.g, ∀ y < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) →
      Tr a (E.layout.cIdx H (t + 1) k j y) → x = y) :
    ∀ x < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) ↔
      x = E.cell (runI M (initList M s) (t + 1)) k j := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.sh_step_cell ha ht _ (E.run_good s t) hrow hS hk hj1 hj2 hamo

/-- **Positive shift step on a real run (L3⁺).** Let $M$ be a finite multi-stack Turing machine
and $E$ an encoding of $M$ with $K$ numbered stacks, tables $sa$, $pl$, $cn$, $pu$ and $N$
situations, let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment satisfying
the cell-shift clause family of the layout of $E$ with these tables and bounds $N$, $T$, $H$.
Call a variable true when its index is less than the length of $a$ and $a$ is true there. Write
$S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for the cell
variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and
$\mathrm{cell}(c, k, j)$ for the code at depth $j$ of the stack numbered $k$ of a configuration
$c$ ($0$ if there is none). Fix an input list $s$, let $c_n$ be the configuration after $n$
idle-extended steps of $M$ from the initial configuration on $s$, and let $i$ be the situation
index of $c_t$. Suppose that every stack of $c_t$ has length at most $H - d$, where $d$ is the
window depth of $M$, that $C[t, k', j', \mathrm{cell}(c_t, k', j')]$ is true for all $k' < K$
and $j' < H$, and that $S[t, i]$ is true. Then for every $k < K$ and every $j$ with
$pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$, the variable
$C[t + 1, k, j, \mathrm{cell}(c_{t+1}, k, j)]$ is true. Subtraction is truncated at $0$. -/
theorem sh_step_run_pos {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t)))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.sh_hold ha ht _ (E.run_good s t) hrow hS hk hj1 hj2

end Enc

/-! ### S-definition forcing (D3Fam family shape: `¬X[t, la i] ∨ ⋁ ¬C[t,k,j,wa i k j] ∨ X[t+1, na i]`) -/

/-- **Transition clauses force the next label.** Let $L$ be a layout with $K$ stacks and window
depth $d$, let $\mathrm{la}, \mathrm{na} : \mathbb{N} \to \mathbb{N}$ and
$\mathrm{wa} : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be tables, and let $a$ be
an assignment satisfying the transition clause family of $L$, $\mathrm{la}$, $\mathrm{na}$ and
$\mathrm{wa}$ for bounds $T$, $H$ and $N$. Write $X[t, b]$ and $C[t, k, j, x]$ for the
label/state and cell variables at height $H$. Suppose $t < T$, $i < N$, $X[t, \mathrm{la}(i)]$ is
true under $a$, and for every $n < Kd$, writing $q = \lfloor n / d \rfloor$ and
$r = n \bmod d$, the variable $C[t, q, r, \mathrm{wa}(i, q, r)]$ is true under $a$. Then
$X[t + 1, \mathrm{na}(i)]$ is true under $a$.

The window literals are indexed by $n$ exactly as in the clause, and no one-hot hypothesis on $a$
is needed. -/
theorem fam_force {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    {a : List Bool} (ha : cnfSat (Family.family L la na wa T H N) a) {t i : ℕ} (ht : t < T)
    (hi : i < N) (hX : Tr a (L.xIdx H t (la i)))
    (hW : ∀ n < L.KK * L.d, Tr a (L.cIdx H t (n / L.d) (n % L.d) (wa i (n / L.d) (n % L.d)))) :
    Tr a (L.xIdx H (t + 1) (na i)) := by
  have hm : Family.denseClause (L.numVars T H) (Family.lits L la na wa H t i) ∈
      Family.family L la na wa T H N :=
    List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  unfold Family.lits at hp
  obtain ⟨j, hj, hjp⟩ := List.mem_map.1 hp
  rw [List.mem_range] at hj
  simp only [Prod.mk.injEq] at hjp
  obtain ⟨rfl, rfl⟩ := hjp
  have hn : L.nLits - 1 = L.KK * L.d + 1 := by unfold Family.Layout.nLits; omega
  have hj2 : j < L.KK * L.d + 2 := hj
  unfold Tr at hX hW ⊢
  by_cases h0 : j = 0
  · subst h0
    simp only [Family.litPos, ite_true] at hab
    rw [hX] at hab
    simp [hn] at hab
  · by_cases h1 : j ≤ L.KK * L.d
    · simp only [Family.litPos, ite_eq_right h0, ite_eq_left h1] at hab
      rw [hW (j - 1) (by omega)] at hab
      have : j ≠ L.nLits - 1 := by omega
      simp [this] at hab
    · have hj' : j = L.KK * L.d + 1 := by omega
      simp only [Family.litPos, ite_eq_right h0, ite_eq_right h1] at hab
      rw [hj', hn] at hab
      simpa using hab

/-- **Transition clauses force the next label, stack-and-depth form.** Let $L$ be a layout with
$K$ stacks and window depth $d$, let $\mathrm{la}, \mathrm{na} : \mathbb{N} \to \mathbb{N}$ and
$\mathrm{wa} : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be tables, and let $a$ be
an assignment satisfying the transition clause family of $L$, $\mathrm{la}$, $\mathrm{na}$ and
$\mathrm{wa}$ for bounds $T$, $H$ and $N$. Write $X[t, b]$ and $C[t, k, j, x]$ for the
label/state and cell variables at height $H$. If $t < T$, $i < N$, $X[t, \mathrm{la}(i)]$ is true
under $a$, and $C[t, k, j, \mathrm{wa}(i, k, j)]$ is true under $a$ for all $k < K$ and $j < d$,
then $X[t + 1, \mathrm{na}(i)]$ is true under $a$. -/
theorem fam_force_kj {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    {a : List Bool} (ha : cnfSat (Family.family L la na wa T H N) a) {t i : ℕ} (ht : t < T)
    (hi : i < N) (hX : Tr a (L.xIdx H t (la i)))
    (hW : ∀ k < L.KK, ∀ j < L.d, Tr a (L.cIdx H t k j (wa i k j))) :
    Tr a (L.xIdx H (t + 1) (na i)) :=
  fam_force ha ht hi hX fun n hn =>
    hW _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hn; exact hn)) _
      (Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hn))

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **The code of a configuration holds in a row.** Given an encoding of a machine $M$, an
assignment $a$, a height $H$, a time $t$ and a configuration $c$ of $M$, the code of $c$ holds in
row $t$ when the label/state variable of row $t$ (at height $H$) whose index is the combined
(label, state) code of $c$ is true under $a$. -/
def CodeHolds (a : List Bool) (H t : ℕ) (c : M.Cfg) : Prop :=
  Tr a (E.layout.xIdx H t (E.code c))

/-- **L2 (S-definition, positive).** Let $E$ be an encoding of the machine $M$ with $K$ stacks and
layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$, let $W$ be
the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state variables and
$C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$. For a
configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the code
of its cell at stack $k$ and depth $j$. Let $T, t \in \mathbb{N}$ with $t < T$, and let the
assignment $a$ satisfy the transition clause family of $L$ for $T$, $H$ and the number $N$ of
situations, with the current-label table $\mathrm{la}$ and the window table $\mathrm{wa}$ of $E$,
and with the table $\mathrm{sa}$ of $E$ (where $\mathrm{sa}(i)$ is the position of the variable of
situation $i$ in the label/state block) in place of the next-label table. Let $c$ be a good
configuration with situation index $i$ such that $X[t, \kappa(c)]$ is true under $a$ and
$C[t, k, j, \gamma_c(k, j)]$ is true under $a$ for all $k < K$ and $j < H$. Then the variable
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$. -/
theorem sd_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t c) (hrow : E.CellsHold a H t (E.cell c)) :
    Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))) := by
  obtain ⟨hi, hla, hwa⟩ := E.sitIdx_spec c hc
  refine fam_force_kj ha ht hi ?_ fun k hk j hj => ?_
  · rw [hla]; exact hcode
  · rw [hwa k hk j hj]; exact hrow k hk j (lt_of_lt_of_le hj hdH)

/-- **L3 (S-definition, real run).** Let $E$ be an encoding of the machine $M$ with $K$ stacks and
layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$, let $W$ be
the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state variables and
$C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$. For a
configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the code
of its cell at stack $k$ and depth $j$. Fix an input list $s$, let $c_n$ be the configuration
after $n$ steps of the idle-extended run of $M$ from the initial configuration on $s$, let
$T, t \in \mathbb{N}$ with $t < T$, and let $i$ be the situation index of $c_t$. Let the
assignment $a$ satisfy the transition clause family of $L$ for $T$, $H$ and the number $N$ of
situations, with the current-label table $\mathrm{la}$ and the window table $\mathrm{wa}$ of $E$,
and with the table $\mathrm{sa}$ of $E$ (where $\mathrm{sa}(i)$ is the position of the variable of
situation $i$ in the label/state block) in place of the next-label table. If $X[t, \kappa(c_t)]$
is true under $a$ and $C[t, k, j, \gamma_{c_t}(k, j)]$ is true under $a$ for all $k < K$ and
$j < H$, then the variable $X[t + 1, \mathrm{sa}(i)]$ is true under $a$. -/
theorem sd_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a) (ht : t < T)
    (hdH : depth M ≤ H) (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))) :=
  E.sd_hold ha ht _ (E.run_good s t) hdH hcode hrow

/-- **Composition with the shift family.** Let $E$ be an encoding of the machine $M$ with $K$
stacks, layout $L$, $N$ situations and situation tables $\mathrm{la}$, $\mathrm{wa}$,
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$ and $\mathrm{pu}$, let $d$ be the window depth of $M$,
let $H \in \mathbb{N}$ with $d \le H$, and let $T, t \in \mathbb{N}$ with $t < T$. Call a
variable true under an assignment $a$ when its index is less than the length of $a$ and $a$ is
true there. Write $X[r, x]$ for the label/state variable $x$ of row $r$ and $C[r, k, j, x]$ for
the cell variable of row $r$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$). For
a configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the
code of its cell at stack $k$ and depth $j$ ($0$ if there is none). Fix an input list $s$, let
$c_n$ be the configuration after $n$ steps of the idle-extended run of $M$ from the initial
configuration on $s$, and let $i$ be the situation index of $c_t$. Let $a$ satisfy both the
transition clause family of $L$ for $T$, $H$ and $N$ with the tables $\mathrm{la}$ and
$\mathrm{wa}$ and with $\mathrm{sa}$ in place of the next-label table, and the cell-shift clause
family of $L$ with the tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ for $N$,
$T$ and $H$. Suppose that every stack of $c_t$ has length at most $H - d$, that
$X[t, \kappa(c_t)]$ is true, and that $C[t, k', j', \gamma_{c_t}(k', j')]$ is true for all
$k' < K$ and $j' < H$. Then for every $k < K$ and every $j$ with
$\mathrm{pl}(i, k) \le j < H - \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) + \mathrm{pl}(i, k)$,
the variable $C[t + 1, k, j, \gamma_{c_{t+1}}(k, j)]$ is true. Subtraction is truncated at $0$. -/
theorem sdsh_step_run_pos {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t)))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) :=
  E.sh_step_run_pos s ha ht hh hrow (E.sd_step_run s hs ht hdH hcode hrow) hk hj1 hj2

end Enc

/-! ### Update, pushed-fill and overflow forcing (C6, second session): positive literals only -/

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Update forcing (positive).** Let $E$ be an encoding of the machine $M$ with $K$ stacks and
layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$, let $W$ be
the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state variables and
$C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$. For a
configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the code
of its cell at stack $k$ and depth $j$. Let $T, t \in \mathbb{N}$ with $t < T$, and let the
assignment $a$ satisfy the transition clause family of $L$ with the current-label table
$\mathrm{la}$, the next-label table $\mathrm{na}$ and the window table $\mathrm{wa}$ of $E$, for
$T$, $H$ and the number $N$ of situations. Let $c$ be a good configuration with situation index
$i$ such that $X[t, \kappa(c)]$ is true under $a$ and $C[t, k, j, \gamma_c(k, j)]$ is true under
$a$ for all $k < K$ and $j < H$. Then the variable $X[t + 1, \mathrm{na}(i)]$ is true under $a$. -/
theorem upd_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t c) (hrow : E.CellsHold a H t (E.cell c)) :
    Tr a (E.layout.xIdx H (t + 1) (E.na (E.sitIdx c))) := by
  obtain ⟨hi, hla, hwa⟩ := E.sitIdx_spec c hc
  refine fam_force_kj ha ht hi ?_ fun k hk j hj => ?_
  · rw [hla]; exact hcode
  · rw [hwa k hk j hj]; exact hrow k hk j (lt_of_lt_of_le hj hdH)

/-- **Update forcing, real run.** Let $E$ be an encoding of the machine $M$ with $K$ stacks and
layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$, let $W$ be
the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state variables and
$C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$. For a
configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the code
of its cell at stack $k$ and depth $j$. Fix an input list $s$, let $c_n$ be the configuration
after $n$ steps of the idle-extended run of $M$ from the initial configuration on $s$, let
$T, t \in \mathbb{N}$ with $t < T$, and suppose every stack of $c_t$ has length at most $H - d$.
Let the assignment $a$ satisfy the transition clause family of $L$ with the current-label table
$\mathrm{la}$, the next-label table $\mathrm{na}$ and the window table $\mathrm{wa}$ of $E$, for
$T$, $H$ and the number $N$ of situations. If $X[t, \kappa(c_t)]$ is true under $a$ and
$C[t, k, j, \gamma_{c_t}(k, j)]$ is true under $a$ for all $k < K$ and $j < H$, then the variable
$X[t + 1, \kappa(c_{t+1})]$ is true under $a$. -/
theorem upd_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a H (t + 1) (runI M (initList M s) (t + 1)) := by
  have h := E.upd_hold ha ht _ (E.run_good s t) hdH hcode hrow
  unfold CodeHolds
  rw [(E.table_agree_run H s t hh).2.2.2.1]
  exact h

end Enc

/-- **Pushed-fill forcing.** Let $L$ be a layout with $A$ label/state variables, $K$ stacks and
$g$ symbol codes, let $\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ be situation tables and
$N, T, H \in \mathbb{N}$, and write $W = A + KHg$, $X[t, x] = tW + x$ and
$C[t, k, j, x] = tW + A + (kH + j)g + x$. If the assignment $a$ satisfies the cell-shift family
of these data, $t < T$, $i < N$, $k < K$, $j < \mathrm{pl}(i, k)$ and the variable
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$, then the variable
$C[t + 1, k, j, \mathrm{pu}(i, k, j)]$ is true under $a$.

Only the situation literal is read. -/
theorem pf_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k j : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK) (hj : j < pl i k)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) : Tr a (L.cIdx H (t + 1) k j (pu i k j)) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.pfLits L sa pu H t i k j) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.pfLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hS] at hab; simp at hab
  · exact hab

/-- **Overflow forcing.** Let $L$ be a layout with $K$ stacks, let $\mathrm{sa}$, $\mathrm{pl}$,
$\mathrm{cn}$ and $\mathrm{pu}$ be situation tables, and let $a$ be an assignment satisfying the
cell-shift clause family of $L$ and these tables for bounds $N$, $T$ and $H$. Write $X[t, b]$ and
$C[t, k, j, x]$ for the label/state and cell variables at height $H$. If $t < T$, $i < N$,
$k < K$, $r < \mathrm{cn}(i, k) - \mathrm{pl}(i, k)$ and the situation variable
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$, then the variable
$C[t + 1, k, H - \mathrm{cn}(i, k) + \mathrm{pl}(i, k) + r, 0]$ is true under $a$, where symbol
code $0$ is the empty cell. Subtraction is truncated at zero. -/
theorem ov_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k r : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK) (hr : r < cn i k - pl i k)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) :
    Tr a (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.ovLits L sa pl cn H t i k r) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
      ⟨r, List.mem_range.2 hr, rfl⟩))
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.ovLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hS] at hab; simp at hab
  · exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Pushed-fill forcing for a good configuration.** Let $E$ be an encoding of the machine $M$
with $K$ stacks and layout $L$, let $H \in \mathbb{N}$, let $W$ be the row width of $L$ at height
$H$, and write $X[t, x] = tW + x$ for the label/state variables and $C[t, k, j, x]$ for the cell
variable of row $t$, stack $k$, depth $j$ and symbol code $x$. Let $T, t \in \mathbb{N}$ with
$t < T$, let the assignment $a$ satisfy the cell-shift family of $E$ (tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations) for $T$ and $H$, and let $c$ be a
good configuration with situation index $i$ such that $X[t + 1, \mathrm{sa}(i)]$ is true under
$a$. Then for all $k < K$ and $j < \mathrm{pl}(i, k)$ the variable $C[t + 1, k, j, r]$ is true
under $a$, where $r$ is the entry at stack $k$ and depth $j$ of the table-driven row update, at
height $H$ and for situation $i$, of the cell codes of $c$. -/
theorem pf_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj : j < E.pl (E.sitIdx c) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j = E.pu (E.sitIdx c) k j := by
    unfold tabRow; rw [ite_eq_left hj]
  rw [htab]
  exact pf_force ha ht (E.sitIdx_spec c hc).1 hk hj hS

/-- **Overflow cells of the next row hold the table value.** Let $E$ be an encoding of a machine
$M$ with $K$ stacks and window depth $d$, and let $a$ be an assignment satisfying the cell-shift
clause family of $E$'s layout and tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$,
$\mathrm{pu}$ for $E$'s number of situations and bounds $T$ and $H$. Write $X[t, b]$ and
$C[t, k, j, x]$ for the label/state and cell variables at height $H$. Let $t < T$, let $c$ be a
configuration of $M$ all of whose stack symbols have codes, suppose $d \le H$, let $i$ be the
situation index of $c$, and suppose $X[t + 1, \mathrm{sa}(i)]$ is true under $a$. Then for every
$k < K$ and every $j$ with
$H - \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) + \mathrm{pl}(i, k) \le j < H$, the variable
$C[t + 1, k, j, x]$ is true under $a$, where $x$ is the value at $(k, j)$ of the table-driven row
update at height $H$ of the cells of $c$ for situation $i$. Subtraction is truncated at zero.

At these depths the table-driven row update is $0$, the empty cell. -/
theorem ov_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK)
    (hj1 : H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have hp := E.pl_le (E.sitIdx c) k
  have hq := E.cn_le (E.sitIdx c) k
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j = 0 := by
    unfold tabRow; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [htab]
  have := ov_force ha ht (E.sitIdx_spec c hc).1 hk
    (r := j - (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k)) (by omega) hS
  rwa [show H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k +
    (j - (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k)) = j by omega] at this

/-- **Pushed-fill forcing on a real run.** Let $E$ be an encoding of the machine $M$ with $K$
stacks and layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$,
let $W$ be the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state
variables and $C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol
code $x$. Fix an input list $s$, let $c_n$ be the configuration after $n$ steps of the
idle-extended run of $M$ from the initial configuration on $s$, let $T, t \in \mathbb{N}$ with
$t < T$, let $i$ be the situation index of $c_t$, and suppose every stack of $c_t$ has length at
most $H - d$. Let the assignment $a$ satisfy the cell-shift family of $E$ (tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations) for $T$ and $H$, and suppose
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$. Then for all $k < K$ and $j < \mathrm{pl}(i, k)$ the
variable $C[t + 1, k, j, x]$ is true under $a$, where $x$ is the code of the cell of $c_{t+1}$ at
stack $k$ and depth $j$ (code $0$ if that cell is empty). -/
theorem pf_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj : j < E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  have := E.pl_le (E.sitIdx (runI M (initList M s) t)) k
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.pf_hold ha ht _ (E.run_good s t) hS hk hj

/-- **Overflow cells of the next row on a real run.** Let $E$ be an encoding of a machine $M$ with
$K$ stacks and window depth $d$, let $s$ be an input, and let $c_t$ be the configuration at step
$t$ of the idle-extended run of $M$ from the initial configuration on input $s$. Let $a$ be an
assignment satisfying the cell-shift clause family of $E$'s layout and tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ for $E$'s number of situations and bounds $T$ and $H$,
and write $X[t, b]$ and $C[t, k, j, x]$ for the label/state and cell variables at height $H$.
Suppose $t < T$, every stack of $c_t$ has length at most $H - d$, $d \le H$, and
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$, where $i$ is the situation index of $c_t$. Then for
every $k < K$ and every $j$ with
$H - \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) + \mathrm{pl}(i, k) \le j < H$, the variable
$C[t + 1, k, j, x]$ is true under $a$, where $x$ is the code of the cell of stack number $k$ at
depth $j$ from the top in $c_{t+1}$ ($0$ if that cell is empty). Subtraction is truncated at
zero. -/
theorem ov_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK)
    (hj1 : H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) +
      E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j) (hj2 : j < H) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j hj2]
  exact E.ov_hold ha ht _ (E.run_good s t) hdH hS hk hj1 hj2

end Enc

/-! ### Stack cap `H` (P2, corrected 2026-09-30) and the `depth_cover` assembly -/

/-- **Stack cap.** For natural numbers $m$, $T$ and $d$ (an input bound, a run length and a
per-step growth), the stack cap is $H = m + (T + 1) d + 1$.

It is used with $d$ the window depth of the machine. -/
def capH (m T d : ℕ) : ℕ := m + (T + 1) * d + 1

/-- **Stack heights along a run.** Let $M$ be a finite TM2 machine with window depth $d$, let $c$
be a configuration and $k$ a stack. For every $t \in \mathbb{N}$, stack $k$ of the configuration
reached from $c$ after $t$ steps of the idle-extended run has length at most the length of stack
$k$ of $c$ plus $t \cdot d$. -/
theorem runI_height {M : FinTM2} (c : M.Cfg) (k : M.K) :
    ∀ t, ((runI M c t).stk k).length ≤ (c.stk k).length + t * depth M
  | 0 => by simp [runI]
  | t + 1 => by
    have h1 := stepI_height (runI M c t) k
    have h2 := runI_height c k t
    have h3 : (t + 1) * depth M = t * depth M + depth M := Nat.succ_mul _ _
    change ((stepI M (runI M c t)).stk k).length ≤ _
    omega

theorem initList_height {M : FinTM2} (s : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M s).stk k).length ≤ s.length := by
  by_cases hk : k = M.k₀
  · subst hk; simp [initList]
  · simp [initList, hk]

/-- **Stack heights are at most the cap minus the window depth.** Let $M$ be a finite
multi-stack Turing machine with window depth $d$, let $m$, $T$ and $t$ be natural numbers with
$t \le T$, and let $s$ be an input of length at most $m$. In the idle-extended run of $M$ from the
initial configuration on input $s$, every stack of the configuration at step $t$ has length at
most $H - d$, where $H = m + (T + 1) d + 1$ is the stack cap for input bound $m$, run length $T$
and per-step growth $d$. -/
theorem capH_height {M : FinTM2} {m T t : ℕ} (s : List (M.Γ M.k₀)) (hs : s.length ≤ m)
    (ht : t ≤ T) (k : M.K) :
    ((runI M (initList M s) t).stk k).length ≤ capH m T (depth M) - depth M := by
  have h1 := runI_height (initList M s) k t
  have h2 := initList_height s k
  have h3 : t * depth M ≤ T * depth M := Nat.mul_le_mul_right _ ht
  have h4 : (T + 1) * depth M = T * depth M + depth M := Nat.succ_mul _ _
  unfold capH; omega

theorem depth_le_capH (M : FinTM2) (m T : ℕ) : depth M ≤ capH m T (depth M) := by
  have h4 : (T + 1) * depth M = T * depth M + depth M := Nat.succ_mul _ _
  unfold capH; omega

/-- **Stack-cap constraint 1.** For natural numbers $\ell$, $m$, $T$ and $d$ with $\ell \le m$, we
have $\ell + (T + 1) d \le H$, where $H = m + (T + 1) d + 1$ is the stack cap for input bound $m$,
run length $T$ and per-step growth $d$. -/
theorem capH_c1 {l m T d : ℕ} (hl : l ≤ m) : l + (T + 1) * d ≤ capH m T d := by
  unfold capH; omega

/-- **Stack-cap constraint 2.** For natural numbers $m$, $T$ and $d$ with $T \ge 1$, the stack cap
$H = m + (T + 1) d + 1$ for input bound $m$, run length $T$ and per-step growth $d$ satisfies
$2d \le H$. -/
theorem capH_c2 {m T d : ℕ} (hT : 1 ≤ T) : 2 * d ≤ capH m T d := by
  have h3 : 1 * d ≤ T * d := Nat.mul_le_mul_right _ hT
  have h4 : (T + 1) * d = T * d + d := Nat.succ_mul _ _
  unfold capH; omega

/-- **The three depth regions cover every depth exactly once.** Let $p, q, H, j$ be natural
numbers with $j < H$, and let $m = H - \max(p, q) + p$, where the subtraction is truncated at
$0$. Then $j$ lies in exactly one of the ranges $j < p$ (pushed fill), $p \le j < m$ (in-range
shift) and $m \le j < H$ (overflow).

These are the depth hypotheses of the pushed-fill, in-range shift and overflow lemmas; nothing is
assumed about $p$, $q$ and $H$. -/
theorem region_cover (p q H j : ℕ) (hj : j < H) :
    (j < p ∨ (p ≤ j ∧ j < H - max p q + p) ∨ (H - max p q + p ≤ j ∧ j < H)) ∧
    ¬ (j < p ∧ p ≤ j) ∧ ¬ (j < p ∧ H - max p q + p ≤ j) ∧
    ¬ (j < H - max p q + p ∧ H - max p q + p ≤ j) := by
  omega

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Cell literals propagate one step along the real run.** Let $E$ be an encoding of a machine
$M$ with window depth $d$, let $s$ be a list of symbols of the input stack of $M$, and for each
$n$ let $c_n$ be the configuration after $n$ steps of the idle-extended run of $M$ from its
initial configuration on $s$. Let $T, H, t$ be natural numbers with $t < T$ and $d \le H$.
Suppose an assignment $a$ satisfies the transition clause family of $E$ with the
situation-variable table $\mathrm{sa}$ in place of the next-label table (the S-definition family)
at $T$, $H$ and the number $N$ of situations of $E$, and satisfies the cell-shift clause family
of $E$ at $N$, $T$, $H$. Suppose also that every stack of $c_t$ has length at most $H - d$, that
the code literal of $c_t$ holds in row $t$ (the label/state variable of row $t$ for the code of
$c_t$ is true under $a$), and that the cell literals of $c_t$ hold in row $t$ (for every stack
number $k$ below the number of stacks and every depth $j < H$, the cell variable of row $t$ for
stack $k$, depth $j$ and the code of the symbol of $c_t$ there, $0$ if there is none, is true
under $a$). Then the cell literals of $c_{t+1}$ hold in row $t + 1$. -/
theorem cells_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CellsHold a H (t + 1) (E.cell (runI M (initList M s) (t + 1))) := by
  have hS := E.sd_step_run s hs ht hdH hcode hrow
  intro k hk j hj
  rcases (region_cover (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) H j hj).1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact E.pf_step_run s ha ht hh hdH hS hk h
  · exact E.sh_step_run_pos s ha ht hh hrow hS hk h1 h2
  · exact E.ov_step_run s ha ht hh hdH hS hk h1 h2

/-- **One-step invariant.** Fix an encoding $E$ of a machine $M$ with $K$ stacks, window depth $d$
and $N$ situations, natural numbers $T$, $H$, $t$ with $t < T$ and $d \le H$, an assignment $a$
and an input list $s$, and let $c_t$ be the configuration at time $t$ of the idle-extended run of
$M$ from the start configuration on $s$.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If every stack of $c_t$ has length at most $H - d$ and $c_t$ is tracked in row $t$, then
$c_{t+1}$ is tracked in row $t + 1$. -/
theorem row_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a H (t + 1) (runI M (initList M s) (t + 1)) ∧
      E.CellsHold a H (t + 1) (E.cell (runI M (initList M s) (t + 1))) :=
  ⟨E.upd_step_run s hu ht hh hdH hcode hrow, E.cells_step_run s hs ha ht hh hdH hcode hrow⟩

/-- **One-step invariant at the stack cap.** Fix an encoding $E$ of a machine $M$ with $K$ stacks,
window depth $d$ and $N$ situations, natural numbers $m$, $T$, $t$ with $t < T$, an assignment
$a$ and an input list $s$ of length at most $m$. Let $H = m + (T + 1)d + 1$ be the stack cap and
let $c_t$ be the configuration at time $t$ of the idle-extended run of $M$ from the start
configuration on $s$.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If $c_t$ is tracked in row $t$, then $c_{t+1}$ is tracked in row $t + 1$. -/
theorem row_step_capH {m T t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀)) (hsm : s.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (ht : t < T)
    (hcode : E.CodeHolds a (capH m T (depth M)) t (runI M (initList M s) t))
    (hrow : E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a (capH m T (depth M)) (t + 1) (runI M (initList M s) (t + 1)) ∧
      E.CellsHold a (capH m T (depth M)) (t + 1) (E.cell (runI M (initList M s) (t + 1))) :=
  E.row_step_run s hu hs ha ht (fun k => capH_height s hsm ht.le k) (depth_le_capH M m T)
    hcode hrow

end Enc

/-! ### Row-`t` induction (C6): chains `row_step_run`; row 0 is `Row0`, derived from the init family
(`init_obl`, below) -/

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Row-0 obligation.** For an encoding $E$ of a machine $M$ with $K$ stacks, an assignment $a$, a
height $H$ and an input list $s$, let $c$ be the start configuration of $M$ on $s$. The row-0
obligation says that, in the layout of $E$ at height $H$, the literal of the (label, state) code
of $c$ in row $0$ is true under $a$ and, for every stack number $k < K$ and depth $j < H$, the
literal of the cell code of $c$ at stack $k$ and depth $j$ in row $0$ is true under $a$.

This is a positive form: the literals of the other cell codes are not required to be false. -/
def Row0 (a : List Bool) (H : ℕ) (s : List (M.Γ M.k₀)) : Prop :=
  E.CodeHolds a H 0 (initList M s) ∧ E.CellsHold a H 0 (E.cell (initList M s))

/-- **Init obligation, input pinned.** Let $E$ be an encoding of a machine $M$ with window depth
$d$, let $a$ be an assignment, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and
let $m, T$ be natural numbers, and put $H = m + (T + 1)d + 1$. The init obligation for $a$, $x$,
$Y$, $m$ and $T$ holds when there is a list $y$ of symbols of $Y$ with $|x| + |y| \le m$ such that
the row-0 obligation holds for $a$ at height $H$ and the input $x$ followed by $y$: under $a$, the
code literal of row $0$ and the cell literals of row $0$ at every depth below $H$ are true for the
initial configuration of $M$ on that input. -/
def InitObl (a : List Bool) (x Ys : List (M.Γ M.k₀)) (m T : ℕ) : Prop :=
  ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
    E.Row0 a (capH m T (depth M)) (x ++ y)

/-- **Row-$t$ induction.** Fix an encoding $E$ of a machine $M$ with $K$ stacks, window depth $d$
and $N$ situations, natural numbers $T$ and $H$ with $d \le H$, an assignment $a$ and an input list
$s$, and let $c_t$ be the configuration at time $t$ of the idle-extended run of $M$ from the start
configuration on $s$.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If, for every $t < T$, every stack of $c_t$ has length at most $H - d$, and the row-0 obligation
holds for $a$, height $H$ and the input $s$, then $c_t$ is tracked in row $t$ for every
$t \le T$. -/
theorem rows_run {T H : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hdH : depth M ≤ H) (h0 : E.Row0 a H s) :
    ∀ t ≤ T, E.CodeHolds a H t (runI M (initList M s) t) ∧
      E.CellsHold a H t (E.cell (runI M (initList M s) t)) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro ht
    have hlt : t < T := Nat.lt_of_succ_le ht
    obtain ⟨hc, hr⟩ := ih hlt.le
    exact E.row_step_run s hu hs ha hlt (hh t hlt) hdH hc hr

/-- **Row induction at the stack cap.** Fix an encoding $E$ of a machine $M$ with $K$ stacks,
window depth $d$ and $N$ situations, natural numbers $m$ and $T$, an assignment $a$ and an input
list $s$ of length at most $m$. Let $H = m + (T + 1)d + 1$ be the stack cap and let $c_t$ be the
configuration at time $t$ of the idle-extended run of $M$ from the start configuration on $s$.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If the row-0 obligation holds for $a$, height $H$ and the input $s$, then $c_t$ is tracked in row
$t$ for every $t \le T$. -/
theorem rows_capH {m T : ℕ} {a : List Bool} (s : List (M.Γ M.k₀)) (hsm : s.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (h0 : E.Row0 a (capH m T (depth M)) s) :
    ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M s) t) ∧
      E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M s) t)) :=
  E.rows_run s hu hs ha (fun _ ht k => capH_height s hsm ht.le k) (depth_le_capH M m T) h0

/-- **Run tracking from the init obligation.** Fix an encoding $E$ of a machine $M$ with $K$
stacks, window depth $d$ and $N$ situations, lists $x$ and $Y$ of input symbols, natural numbers
$m$ and $T$, and an assignment $a$, and let $H = m + (T + 1)d + 1$ be the stack cap.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If the init obligation holds for $a$, $x$, $Y$, $m$ and $T$, then there is a list $y$ of input
symbols, each occurring in $Y$, such that the concatenation $xy$ has length at most $m$ and, for
every $t \le T$, the configuration at time $t$ of the idle-extended run of $M$ from the start
configuration on $xy$ is tracked in row $t$. -/
theorem rows_of_init {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool}
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : E.InitObl a x Ys m T) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M (x ++ y)) t) ∧
        E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M (x ++ y)) t)) := by
  obtain ⟨y, hy, hsm, h0⟩ := hI
  exact ⟨y, hy, hsm, E.rows_capH (x ++ y) hsm hu hs ha h0⟩

end Enc

/-! ### The init family (row 0) and its semantics: discharges `InitObl` with the input pinned -/

/-- **Satisfying a concatenation of CNF formulas.** For dense CNF formulas $\varphi$ and $\psi$
and a finite bit sequence $a$, $a$ satisfies the concatenation of $\varphi$ and $\psi$ (the
clauses of $\varphi$ followed by those of $\psi$) if and only if $a$ satisfies both $\varphi$ and
$\psi$. -/
theorem cnfSat_append {φ ψ : CNF} {a : List Bool} : cnfSat (φ ++ ψ) a ↔ cnfSat φ a ∧ cnfSat ψ a := by
  simp only [cnfSat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- **Positive dense unit clauses force their variable.** If an assignment $a$ satisfies a CNF
formula $\varphi$ containing the dense clause over $V$ variables built from the literal list
whose only entry is the pair $(v, \mathrm{true})$, then variable $v$ is true under $a$. -/
theorem unit_force {V v : ℕ} {φ : CNF} {a : List Bool} (h : cnfSat φ a)
    (hm : Family.denseClause V [(v, true)] ∈ φ) : Tr a v := by
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (h _ hm)
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Index of the empty-cell variable of the input stack.** For an encoding $E$ and natural numbers
$H$ and $j$, this is the index, in the layout of $E$ at height $H$, of the cell variable for row
$0$, the stack number of the input stack, depth $j$ from the top and symbol code $0$ (the empty
cell). -/
def zIdx (H j : ℕ) : ℕ := E.layout.cIdx H 0 (E.kc M.k₀) j 0

/-- **Start-code clause of the init family.** Let $E$ be an encoding of a machine $M$ and let
$T, H$ be natural numbers. The start-code clause is the CNF formula with a single clause: the
dense clause over the $(T + 1)W$ variables of the layout of $E$, where $W$ is its row width at
height $H$, whose only literal is the positive literal of the label/state variable of row $0$ for
the code under $E$ of the pair formed by the main label of $M$ and its initial state. -/
def initCode (T H : ℕ) : CNF :=
  [Family.denseClause (E.layout.numVars T H) [(E.layout.xIdx H 0 (E.lc (some M.main,
      M.initialState)), true)]]

/-- **Empty-stack clauses of the init family.** Let $E$ be an encoding of a machine $M$ with $K$
numbered stacks and let $T, H$ be natural numbers. The empty-stack clauses form the CNF formula
that lists, for each stack number $k < K$ other than the number of the input stack in increasing
order and, within it, each depth $j < H$ in increasing order, the dense clause over the
$(T + 1)W$ variables of the layout of $E$, where $W$ is its row width at height $H$, whose only
literal is the positive literal of the cell variable of row $0$ for stack $k$, depth $j$ and code
$0$, the empty cell. They ask that every stack other than the input stack be empty in row $0$. -/
def initOther (T H : ℕ) : CNF :=
  ((List.range E.KK).filter (· ≠ E.kc M.k₀)).flatMap fun k =>
    (List.range H).map fun j => Family.denseClause (E.layout.numVars T H) [(E.layout.cIdx H 0 k j 0, true)]

/-- **Input clauses of the init family.** Let $E$ be an encoding of a machine $M$, let
$x = x_0 x_1 \cdots x_{n-1}$ be a list of symbols of the input stack of $M$, and let $T, H$ be
natural numbers. The input clauses form the CNF formula that lists, for $j = 0, 1, \dots, n - 1$
in order, the dense clause over the $(T + 1)W$ variables of the layout of $E$, where $W$ is its
row width at height $H$, whose only literal is the positive literal of the cell variable of row
$0$ for the input stack, depth $j$ and the symbol code under $E$ of $x_j$. They pin the input $x$
at the top of the input stack, one cell at a time. -/
def initIn (x : List (M.Γ M.k₀)) (T H : ℕ) : CNF :=
  (List.range x.length).map fun j => Family.denseClause (E.layout.numVars T H)
    [(E.layout.cIdx H 0 (E.kc M.k₀) j ((x[j]?).elim 0 (E.enc M.k₀)), true)]

/-- **Certificate clauses of the init family.** Let $E$ be an encoding of a machine $M$, let $x$
and $Y$ be lists of symbols of the input stack of $M$, and let $m, T, H$ be natural numbers. For a
depth $j$ and a symbol code $c$, write $C_0[j, c]$ for the cell variable of row $0$, input stack,
depth $j$ and code $c$ in the layout of $E$ at height $H$, and let $e$ be the symbol code of $E$
on the input stack. The certificate clauses form the CNF formula that lists, for each depth
$j = |x|, |x| + 1, \dots, m - 1$ in order (none if $m \le |x|$), the dense clause over the
$(T + 1)W$ variables of the layout, where $W$ is its row width at height $H$, whose literals are
$C_0[j, 0]$ followed by $C_0[j, e(z)]$ for each $z$ in $Y$ in order, all positive.

Code $0$ is the empty cell, so the clause for $j$ asks that depth $j$ of the input stack be empty
or hold a symbol of $Y$. -/
def initCert (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  (List.range (m - x.length)).map fun i => Family.denseClause (E.layout.numVars T H)
    ((E.zIdx H (x.length + i), true) ::
      Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true))

/-- **Prefix clauses of the init family.** Let $E$ be an encoding of a machine $M$, let $x$ be a
list of symbols of the input stack of $M$, and let $m, T, H$ be natural numbers. For a depth $j$,
write $Z_j$ for the cell variable of row $0$, input stack, depth $j$ and code $0$ (the empty cell)
in the layout of $E$ at height $H$. The prefix clauses form the CNF formula that lists, for
$j = |x|, |x| + 1, \dots, m - 1$ in order (none if $m \le |x|$), the dense clause over the
$(T + 1)W$ variables of the layout, where $W$ is its row width at height $H$, with the literals
$\neg Z_j$ and $Z_{j+1}$. On these depths, an empty cell forces an empty cell one level deeper. -/
def initPre (x : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  (List.range (m - x.length)).map fun i => Family.denseClause (E.layout.numVars T H)
    [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1), true)]

/-- **Length-bound clauses of the init family.** For an encoding $E$ and natural numbers $m$, $T$
and $H$, this is the CNF formula with one clause for each depth $j$ with $m \le j < H$, in
increasing order of $j$: the dense clause over the variables of the transition-clause formula of
the layout of $E$ at bounds $T$ and $H$, built from the single positive literal of the empty-cell
variable of the input stack at depth $j$ in row $0$. -/
def initTail (m T H : ℕ) : CNF :=
  (List.range (H - m)).map fun i => Family.denseClause (E.layout.numVars T H) [(E.zIdx H (m + i),
      true)]

/-- **The row-0 init family of an encoding.** Let $E$ be an encoding of a machine $M$, let $x$ and
$Y$ be lists of symbols of the input stack of $M$, and let $m, T, H$ be natural numbers. The init
family is the CNF formula whose clauses are, in this order, those of the start-code clause at
$(T, H)$, the empty-stack clauses at $(T, H)$, the input clauses of $x$ at $(T, H)$, the
certificate clauses of $x$ and $Y$ at $(m, T, H)$, the prefix clauses of $x$ at $(m, T, H)$ and
the tail clauses at $(m, T, H)$.

Together they ask that row $0$ hold the start code, empty stacks other than the input stack, the
input $x$ at the top of the input stack, cells that are empty or hold a symbol of $Y$ at the
depths $|x| \le j < m$, with an empty cell at such a depth $j$ forcing an empty cell at $j + 1$,
and empty cells at the depths $m \le j < H$. -/
def initFamily (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  E.initCode T H ++ E.initOther T H ++ E.initIn x T H ++ E.initCert x Ys m T H ++
    E.initPre x m T H ++ E.initTail m T H

theorem initList_k₀ (s : List (M.Γ M.k₀)) : (initList M s).stk M.k₀ = s := by
  simp [initList]

theorem initList_ne (s : List (M.Γ M.k₀)) (k : M.K) (hk : k ≠ M.k₀) : (initList M s).stk k = [] := by
  simp [initList, hk]

/-- **Init semantics.** Fix an encoding $E$ of a machine $M$, lists $x$ and $Y$ of symbols of the
input alphabet, natural numbers $m$, $T$, $H$ with $|x| \le m < H$, and an assignment $a$ that
satisfies the init family of $E$ for $x$, $Y$, $m$, $T$ and $H$. Then there is a list $y$ of
input symbols, each occurring in $Y$, such that the concatenation $xy$ has length at most $m$ and
the row-0 obligation holds for $a$, height $H$ and the input $xy$. -/
theorem init_row0 {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} {a : List Bool}
    (hx : x.length ≤ m) (hmH : m < H) (hI : cnfSat (E.initFamily x Ys m T H) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧ E.Row0 a H (x ++ y) := by
  simp only [initFamily, cnfSat_append] at hI
  obtain ⟨⟨⟨⟨⟨hC, hO⟩, hIn⟩, hCe⟩, hP⟩, hTl⟩ := hI
  -- the forced literals
  have tail : ∀ j, m ≤ j → j < H → Tr a (E.zIdx H j) := fun j h1 h2 => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    exact unit_force hTl (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩)
  have pre : ∀ j, x.length ≤ j → j < m → Tr a (E.zIdx H j) → Tr a (E.zIdx H (j + 1)) := by
    intro j h1 h2 hz
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hm : Family.denseClause (E.layout.numVars T H)
        [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1),
            true)] ∈ E.initPre x m T H :=
      List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (hP _ hm)
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
    unfold Tr at hz ⊢
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hz] at hab; simp at hab
    · exact hab
  have cert : ∀ j, x.length ≤ j → j < m → ¬ Tr a (E.zIdx H j) →
      ∃ z, z ∈ Ys ∧ Tr a (E.layout.cIdx H 0 (E.kc M.k₀) j (E.enc M.k₀ z)) := by
    intro j h1 h2 hz
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hm : Family.denseClause (E.layout.numVars T H) ((E.zIdx H (x.length + i), true) ::
        Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true)) ∈
        E.initCert x Ys m T H :=
      List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (hCe _ hm)
    rcases List.mem_cons.1 hp with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd hab hz
    · obtain ⟨z, hz, he⟩ := List.mem_map.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨z, hz, hab⟩
  -- the first `⊥` at or below `|x|`
  have hex : ∃ j, x.length ≤ j ∧ Tr a (E.zIdx H j) := ⟨m, hx, tail m le_rfl hmH⟩
  classical
  let ℓ := Nat.find hex
  have hxℓ : x.length ≤ ℓ := (Nat.find_spec hex).1
  have hℓm : ℓ ≤ m := Nat.find_min' hex ⟨hx, tail m le_rfl hmH⟩
  have zall : ∀ j, ℓ ≤ j → j < H → Tr a (E.zIdx H j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => (Nat.find_spec hex).2
    | succ j hj ih =>
      intro hjH
      by_cases hjm : j < m
      · exact pre j (by omega) hjm (ih (by omega))
      · exact tail _ (by omega) hjH
  have free : ∀ i, i < ℓ - x.length →
      ∃ z, z ∈ Ys ∧ Tr a (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z)) :=
    fun i hi => cert _ (by omega) (by omega) fun hz =>
      Nat.find_min hex (show x.length + i < ℓ by omega) ⟨by omega, hz⟩
  let y : List (M.Γ M.k₀) := List.ofFn fun i : Fin (ℓ - x.length) => Classical.choose (free i i.2)
  have hyl : y.length = ℓ - x.length := List.length_ofFn
  refine ⟨y, fun z hz => ?_, by rw [List.length_append, hyl]; omega, ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    exact (Classical.choose_spec (free i i.2)).1
  · exact unit_force hC (List.mem_singleton.2 rfl)
  · intro k hk j hj
    by_cases hk0 : k = E.kc M.k₀
    · subst hk0
      rw [E.cell_kc, initList_k₀]
      by_cases hjx : j < x.length
      · rw [List.getElem?_append_left hjx]
        exact unit_force hIn (List.mem_map.2 ⟨j, List.mem_range.2 hjx, rfl⟩)
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjx)
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        by_cases hi : i < ℓ - x.length
        · rw [List.getElem?_ofFn, dite_eq_left hi]
          exact (Classical.choose_spec (free i hi)).2
        · rw [List.getElem?_eq_none (by omega)]
          exact zall _ (by omega) hj
    · have hne : E.kd k ≠ M.k₀ := fun h => hk0 (by rw [← h, E.kc_kd k hk])
      unfold cell
      rw [initList_ne _ _ hne]
      exact unit_force hO (List.mem_flatMap.2 ⟨k, List.mem_filter.2 ⟨List.mem_range.2 hk,
        by simpa using hk0⟩, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)

/-- **The init family discharges the init obligation.** Let $E$ be an encoding of a machine $M$
with window depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and let
$m, T$ be natural numbers with $|x| \le m$, and put $H = m + (T + 1)d + 1$. If an assignment $a$
satisfies the init family of $E$ for $x$, $Y$, $m$, $T$ and $H$, then the init obligation holds
for $a$, $x$, $Y$, $m$ and $T$: there is a list $y$ of symbols of $Y$ with $|x| + |y| \le m$ such
that the row-0 obligation holds for $a$ at height $H$ and the input $x$ followed by $y$. -/
theorem init_obl {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool} (hx : x.length ≤ m)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a) : E.InitObl a x Ys m T :=
  E.init_row0 hx (by unfold capH; omega) hI

/-- **A satisfying assignment tracks a certified run.** Let $E$ be an encoding of a machine $M$
with window depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let
$m, T \in \mathbb{N}$ with $|x| \le m$, and let $H = m + (T + 1)d + 1$ be the corrected stack cap.
Write $\mathrm{la}, \mathrm{na}, \mathrm{sa}, \mathrm{wa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$
for the situation tables of $E$ and $N$ for its number of situations. Suppose an assignment $a$
satisfies the following families at bounds $T$ and $H$: the transition clause family of the layout
of $E$ for $N$ situations with tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ (the update
family); the transition clause family for $N$ situations with tables $\mathrm{la}$,
$\mathrm{sa}$, $\mathrm{wa}$ (the S-definition family); the cell-shift clause family for $N$
situations with tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$; and the init
family of $E$ for $x$, $Y$, $m$. Then there is a list $y$ of symbols, each in $Y$, with
$|xy| \le m$ such that for every $t \le T$, if $c_t$ is the configuration after $t$ steps of the
idle-extended run of $M$ from the initial configuration on input $xy$, then under $a$ the variable
of row $t$ for the (label, state) code of $c_t$ is true, and for every stack number $k$ of $E$ and
every depth $j < H$ the variable of row $t$ for stack $k$, depth $j$ and the cell code of $c_t$ at
$(k, j)$ is true. -/
theorem rows_of_initFamily {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool} (hx : x.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M (x ++ y)) t) ∧
        E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M (x ++ y)) t)) :=
  E.rows_of_init hu hs ha (E.init_obl hx hI)

end Enc

/-! ### [C6] Accept (row `T`) and literal faithfulness (2026-10-01, second): every literal of every
family survives into its dense clause; the accept family; soundness `accept_sound` -/

/-! ### Literal faithfulness: no literal of a dense clause is dropped (out of range or shadowed) -/

/-- **Faithful literal list.** A list $\ell$ of literals $(p, b)$, each a variable index
$p \in \mathbb{N}$ with a sign $b$, is faithful for $V \in \mathbb{N}$ when every literal $(p, b)$
of $\ell$ has $p < V$ and the first literal of $\ell$ with index $p$ is $(p, b)$.

Equivalently, every literal of $\ell$ survives into the dense clause over $V$ variables built from
$\ell$: it is in range, and not shadowed by an earlier literal at the same index with the other
sign. -/
def Faithful (V : ℕ) (ls : List (ℕ × Bool)) : Prop :=
  ∀ p b, (p, b) ∈ ls → p < V ∧ ls.lookup p = some b

/-- **Faithful dense clause family.** A CNF formula $\varphi$ is a faithful family over $V$
variables when every clause of $\varphi$ is the dense clause over $V$ variables built from some
list of literals that is faithful for $V$. -/
def FamOK (V : ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∃ ls, c = Family.denseClause V ls ∧ Faithful V ls

/-- **Faithful dense clause family with positive literals.** A CNF formula $\varphi$ is a faithful
family with positive literals over $V$ variables when every clause of $\varphi$ is the dense clause
over $V$ variables built from some list $\ell$ of literals that is faithful for $V$ and contains a
positive literal $(p, \mathrm{true})$ for some $p$. -/
def FamPos (V : ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∃ ls, c = Family.denseClause V ls ∧ Faithful V ls ∧ ∃ p, (p, true) ∈ ls

theorem FamPos.ok {V : ℕ} {φ : CNF} (h : FamPos V φ) : FamOK V φ := fun c hc =>
  let ⟨ls, h1, h2, _⟩ := h c hc
  ⟨ls, h1, h2⟩

/-- **Exact clause semantics.** Let $V \in \mathbb{N}$, let $\ell$ be a list of pairs $(p, b)$ of a
variable index $p$ and a sign $b$ that is faithful for $V$, and let $a$ be a list of Booleans.
Then $a$ satisfies the dense clause over $V$ variables built from $\ell$ if and only if some
$(p, b) \in \ell$ has $p < |a|$ and $a_p = b$. -/
theorem clauseSat_iff {V : ℕ} {ls : List (ℕ × Bool)} {a : List Bool} (h : Faithful V ls) :
    clauseSat (Family.denseClause V ls) a ↔ ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b := by
  refine ⟨clauseSat_dense, fun ⟨p, b, hp, ha⟩ => ⟨p, b, ?_, ha⟩⟩
  obtain ⟨hV, hl⟩ := h p b hp
  unfold Family.denseClause
  rw [List.getElem?_map, List.getElem?_range hV]
  simp [hl]

theorem lookup_of_mem {p : ℕ} {b : Bool} :
    ∀ {ls : List (ℕ × Bool)}, (p, b) ∈ ls → ∃ b', ls.lookup p = some b'
  | [], h => by simp at h
  | (q, c) :: r, h => by
    by_cases hq : p = q
    · subst hq; exact ⟨c, by simp⟩
    · rw [Family.lookup_cons_ne hq]
      rcases List.mem_cons.1 h with h | h
      · exact absurd (Prod.mk.inj h).1 hq
      · exact lookup_of_mem h

theorem faithful_of_pol {V : ℕ} {ls : List (ℕ × Bool)} (hV : ∀ p b, (p, b) ∈ ls → p < V)
    (hb : ∀ p b b', (p, b) ∈ ls → (p, b') ∈ ls → b = b') : Faithful V ls := by
  intro p b hp
  obtain ⟨b', hl⟩ := lookup_of_mem hp
  exact ⟨hV p b hp, by rw [hl, hb p b' b (mem_of_lookup hl) hp]⟩

theorem faithful_pos {V : ℕ} {ls : List (ℕ × Bool)} (h : ∀ p b, (p, b) ∈ ls → p < V ∧ b = true) :
    Faithful V ls :=
  faithful_of_pol (fun p b hp => (h p b hp).1) fun p b b' hp hp' => by
    rw [(h p b hp).2, (h p b' hp').2]

theorem faithful_single {V p : ℕ} {b : Bool} (h : p < V) : Faithful V [(p, b)] := by
  intro q c hq
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  exact ⟨h, by simp⟩

theorem Inc.ge : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Family.Inc lo ls V →
    ∀ p b, (p, b) ∈ ls → lo ≤ p
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, _) :: _, _, ⟨h1, h2⟩, p, b, h => by
    rcases List.mem_cons.1 h with h | h
    · rw [(Prod.mk.inj h).1]; exact h1
    · have := Inc.ge h2 p b h; omega

theorem faithful_of_inc : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Family.Inc lo ls V →
    Faithful V ls
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, c) :: r, _, ⟨h1, h2⟩, p, b, h => by
    have hV := Family.Inc.le h2
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨by omega, by simp⟩
    · have hq := Inc.ge h2 p b h
      obtain ⟨hp, hl⟩ := faithful_of_inc h2 p b h
      exact ⟨hp, by rw [Family.lookup_cons_ne (by omega)]; exact hl⟩

/-- **The all-true assignment satisfies a faithful clause with a positive literal.** Let
$V \in \mathbb{N}$ and let $\ell$ be a list of literals that is faithful for $V$ and contains a
positive literal $(p, \mathrm{true})$. Then the all-true assignment of length $V$ satisfies the
dense clause over $V$ variables built from $\ell$. -/
theorem sat_allTrue {V : ℕ} {ls : List (ℕ × Bool)} (hf : Faithful V ls) (hp : ∃ p, (p, true) ∈ ls) :
    clauseSat (Family.denseClause V ls) (List.replicate V true) := by
  obtain ⟨p, hp⟩ := hp
  refine (clauseSat_iff hf).2 ⟨p, true, hp, ?_⟩
  rw [List.getElem?_replicate, ite_eq_left (hf p true hp).1]

theorem FamPos.allTrue {V : ℕ} {φ : CNF} (h : FamPos V φ) : cnfSat φ (List.replicate V true) := by
  intro c hc
  obtain ⟨ls, rfl, hf, hp⟩ := h c hc
  exact sat_allTrue hf hp

/-! ### The D3 families (update, S-def, shift/overflow/pushed fill) are faithful -/

/-- **Variables of rows up to the time bound.** Let $L$ be a layout, let $T$, $H$, $t$ and $p$ be
natural numbers with $t \le T$, and let $W$ be the number of variables per time step of $L$ at
height $H$. If $p < (t + 1) W$, then $p$ is less than the number of variables of $L$ for bounds
$T$ and $H$. -/
theorem lt_numVars {L : Family.Layout} {T H t p : ℕ} (ht : t ≤ T) (hp : p < (t + 1) * L.rowW H) :
    p < L.numVars T H :=
  lt_of_lt_of_le hp (Nat.mul_le_mul_right _ (by omega))

theorem fam_pos {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    (hwf : ∀ i < N, Family.WF L la na wa H i) :
    FamPos (L.numVars T H) (Family.family L la na wa T H N) := by
  intro c hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  refine ⟨_, rfl, faithful_of_inc (Family.lits_inc (List.mem_range.1 ht)
    (hwf i (List.mem_range.1 hi))), ⟨Family.litPos L la na wa H t i (L.nLits - 1), List.mem_map.2 ⟨L.nLits - 1, List.mem_range.2 ?_, ?_⟩⟩⟩
  · unfold Family.Layout.nLits; omega
  · simp

theorem sh_pos {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} (hwf : Shift.WF L sa pl cn pu N H) :
    FamPos (L.numVars T H) (Shift.shFamily L sa pl cn pu N T H) := by
  intro c hc
  simp only [Shift.shFamily, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨t, ht, i, hi, k, hk, hc⟩ := hc
  simp only [Shift.shBlk, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with (⟨u, hu, x, hx, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨j, hj, rfl⟩
  · have := Shift.inc_drop (cl := (.sh ⟨x, hx⟩ : Shift.CL L.g L.d))
      (Shift.shPos_mono (i := ⟨i, hi⟩) (k := ⟨k,
          hk⟩) ht hwf (Nat.add_lt_of_lt_sub hu) hx) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_sh] at this
    exact ⟨_, rfl, faithful_of_inc this, L.cIdx H (t + 1) k (u + pl i k) x, by simp [Shift.shLits]⟩
  · have := Shift.inc_drop (cl := (.ov : Shift.CL L.g L.d))
      (Shift.ovPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hr) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_ov] at this
    exact ⟨_, rfl, faithful_of_inc this, L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0,
        by simp [Shift.ovLits]⟩
  · have hjd : j < L.d := lt_of_lt_of_le hj (hwf.pl_le i hi k hk)
    have := Shift.inc_drop (cl := (.pf ⟨j, hjd⟩ : Shift.CL L.g L.d))
      (Shift.pfPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hj) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_pf] at this
    exact ⟨_, rfl, faithful_of_inc this, L.cIdx H (t + 1) k j (pu i k j), by simp [Shift.pfLits]⟩

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem enc_lt (k : M.K) (z : M.Γ k) (h : ∃ i, E.dec k i = z) : E.enc k z < E.g := by
  obtain ⟨i, rfl⟩ := h
  rw [E.enc_dec]; have := E.sz_lt_g k; omega

theorem xIdx_lt {T H t u : ℕ} (ht : t ≤ T) (hu : u < E.A0) :
    E.layout.xIdx H t u < E.layout.numVars T H := by
  refine lt_numVars ht ?_
  unfold Family.Layout.xIdx Family.Layout.rowW
  rw [Nat.succ_mul]
  have : E.layout.A = E.A0 + E.N := rfl
  omega

theorem cIdx_lt {T H t k j x : ℕ} (ht : t ≤ T) (hk : k < E.KK) (hj : j < H) (hx : x < E.g) :
    E.layout.cIdx H t k j x < E.layout.numVars T H :=
  lt_numVars ht (Family.cIdx_lt_next_row (L := E.layout) hk hj hx)

theorem upd_pos {T H : ℕ} (hH : depth M ≤ H) :
    FamPos (E.layout.numVars T H) (Family.family E.layout E.la E.na E.wa T H E.N) :=
  fam_pos fun i _ => E.wf_upd hH i

theorem sdef_pos {T H : ℕ} (hH : depth M ≤ H) :
    FamPos (E.layout.numVars T H) (Family.family E.layout E.la E.sa E.wa T H E.N) :=
  fam_pos fun i hi => E.wf_sdef hH i hi

theorem shift_pos {T H : ℕ} (hH : depth M ≤ H) :
    FamPos (E.layout.numVars T H) (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) :=
  sh_pos (E.wf_sh hH)

/-- **The init family is faithful with positive literals.** Let $E$ be an encoding of a machine
$M$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and let $m, T, H \in \mathbb{N}$
with $|x| \le m < H$. Let $V$ be the number of variables of the layout of $E$ at bounds $T$ and
$H$. Then every clause of the init family of $E$ for $x$, $Y$, $m$, $T$, $H$ is the dense clause
over $V$ variables built from a list of literals that is faithful for $V$ and contains a positive
literal; that is, the init family is a faithful family with positive literals over $V$ variables. -/
theorem init_pos {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hx : x.length ≤ m) (hmH : m < H) :
    FamPos (E.layout.numVars T H) (E.initFamily x Ys m T H) := by
  have cl : ∀ k j v, k < E.KK → j < H → v < E.g → E.layout.cIdx H 0 k j v < E.layout.numVars T H :=
    fun k j v hk hj hv => E.cIdx_lt (Nat.zero_le T) hk hj hv
  have e0 : ∀ z : M.Γ M.k₀, E.enc M.k₀ z < E.g := fun z => E.enc_lt _ z (E.input_mem z)
  intro c hc
  simp only [initFamily, List.mem_append] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc) | hc
  · obtain rfl := List.mem_singleton.1 hc
    exact ⟨_, rfl, faithful_single (E.xIdx_lt (Nat.zero_le T) (E.lc_lt _)), _,
        List.mem_singleton.2 rfl⟩
  · obtain ⟨k, hk, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, rfl, faithful_single (cl _ _ _ (List.mem_range.1 (List.mem_filter.1 hk).1)
      (List.mem_range.1 hj) E.g_pos), _, List.mem_singleton.2 rfl⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    have hj := List.mem_range.1 hj
    refine ⟨_, rfl, faithful_single (cl _ _ _ (E.kc_lt _) (by omega) ?_), _,
        List.mem_singleton.2 rfl⟩
    rw [List.getElem?_eq_getElem hj]
    exact e0 _
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    refine ⟨_, rfl, faithful_pos fun p b hp => ?_, _, List.mem_cons_self⟩
    rcases List.mem_cons.1 hp with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨cl _ _ _ (E.kc_lt _) (by omega) E.g_pos, rfl⟩
    · obtain ⟨z, _, he⟩ := List.mem_map.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨cl _ _ _ (E.kc_lt _) (by omega) (e0 z), rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    have h2 := cl (E.kc M.k₀) (x.length + i + 1) 0 (E.kc_lt _) (by omega) E.g_pos
    have hg := E.g_pos
    have h1 : E.zIdx H (x.length + i) + 1 ≤ E.zIdx H (x.length + i + 1) := by
      unfold zIdx Family.Layout.cIdx
      have : (E.kc M.k₀ * H + (x.length + i + 1)) * E.layout.g =
          (E.kc M.k₀ * H + (x.length + i)) * E.layout.g + E.layout.g := by ring
      have : E.layout.g = E.g := rfl
      omega
    exact ⟨_, rfl, faithful_of_inc (lo := 0) ⟨Nat.zero_le _, h1, h2⟩, _,
      List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    exact ⟨_, rfl, faithful_single (cl _ _ _ (E.kc_lt _) (by omega) E.g_pos), _,
      List.mem_singleton.2 rfl⟩

/-! ### The accept family (row `T`): exactly the halted start-state code, exactly `acc` on top of `k₁` -/

/-- **Accepting code.** For an encoding $E$ of a finite stack machine $M$, the accepting code is
the (label, state) code that $E$ assigns to the pair of the halted label and the initial state of
$M$, the label and state of a halted configuration as acceptance reads it. -/
def acode : ℕ := E.lc (none, M.initialState)

/-- **Accept-code clauses.** Let $E$ be an encoding of a finite stack machine $M$ with $A_0$
(label, state) codes, let $c^\ast$ be the code that $E$ assigns to the halted label together with
the initial state of $M$, and let $T, H \in \mathbb{N}$. In the layout of $E$ at height $H$, let
$W$ be the row width, $V = (T + 1)W$ the number of variables, and $X[t, u] = tW + u$ the
label/state variable $u$ at time $t$. The accept-code clauses are the CNF formula listing, for
each $u < A_0$ in increasing order, the dense clause over $V$ variables built from the single
literal $X[T, u]$ if $u = c^\ast$ and $\neg X[T, u]$ otherwise. -/
def accCode (T H : ℕ) : CNF :=
  (List.range E.A0).map fun u => Family.denseClause (E.layout.numVars T H)
    [(E.layout.xIdx H T u, decide (u = E.acode))]

/-- **Accept-cell clauses.** Let $E$ be an encoding of a finite stack machine $M$ with output
stack $k_1$, $g$ symbol codes and stack numbering $\kappa$, let $\alpha$ be a symbol of stack $k_1$
with code $e$, and let $T, H \in \mathbb{N}$. In the layout of $E$ at height $H$, let $W$ be the
row width, $V = (T + 1)W$ the number of variables, and $C[t, k, j, x]$ the variable for stack $k$,
depth $j$ and symbol code $x$ at time $t$. The accept-cell clauses are the CNF formula listing,
for each $x < g$ in increasing order, the dense clause over $V$ variables built from the single
literal $C[T, \kappa(k_1), 0, x]$ if $x = e$ and $\neg C[T, \kappa(k_1), 0, x]$ otherwise. -/
def accCell (acc : M.Γ M.k₁) (T H : ℕ) : CNF :=
  (List.range E.g).map fun x => Family.denseClause (E.layout.numVars T H)
    [(E.layout.cIdx H T (E.kc M.k₁) 0 x, decide (x = E.enc M.k₁ acc))]

/-- **The accept family.** Let $E$ be an encoding of a finite stack machine $M$, let $\alpha$ be a
symbol of the output stack of $M$, and let $T, H \in \mathbb{N}$. The accept family for $\alpha$ at
bounds $T$ and $H$ is the CNF formula formed by the accept-code clauses at $T$ and $H$ followed by
the accept-cell clauses for $\alpha$ at $T$ and $H$. -/
def accFamily (acc : M.Γ M.k₁) (T H : ℕ) : CNF := E.accCode T H ++ E.accCell acc T H

theorem acc_ok {acc : M.Γ M.k₁} {T H : ℕ} (hH : 0 < H) :
    FamOK (E.layout.numVars T H) (E.accFamily acc T H) := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, rfl, faithful_single (E.xIdx_lt le_rfl (List.mem_range.1 hu))⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, rfl, faithful_single (E.cIdx_lt le_rfl (E.kc_lt _) hH (List.mem_range.1 hx))⟩

theorem unit_pol {V p : ℕ} {b : Bool} {φ : CNF} {a : List Bool} (h : cnfSat φ a)
    (hm : Family.denseClause V [(p, b)] ∈ φ) (ht : Tr a p) : b = true := by
  obtain ⟨q, c, hq, hab⟩ := clauseSat_dense (h _ hm)
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  unfold Tr at ht
  rw [ht] at hab
  exact (Option.some.inj hab).symm

/-- **Accept-code clauses pin the (label, state) code.** Let $E$ be an encoding of a finite stack
machine $M$ with $A_0$ (label, state) codes, let $\alpha$ be a symbol of the output stack of $M$,
and let $T, H, u \in \mathbb{N}$ with $u < A_0$. In the layout of $E$ at height $H$, let $X[t, w]$
be the label/state variable $w$ at time $t$, and call a variable $v$ true under an assignment $a$
when $v < |a|$ and $a_v$ is true. If an assignment $a$ satisfies the accept family for $\alpha$
at bounds $T$ and $H$, and $X[T, u]$ is true under $a$, then $u$ is the code that $E$ assigns to
the halted label together with the initial state of $M$. -/
theorem acc_code {acc : M.Γ M.k₁} {T H u : ℕ} {a : List Bool} (h : cnfSat (E.accFamily acc T H) a)
    (hu : u < E.A0) (ht : Tr a (E.layout.xIdx H T u)) : u = E.acode :=
  of_decide_eq_true (unit_pol h (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_range.2 hu,
      rfl⟩)) ht)

/-- **Accept-cell clauses pin the top output symbol.** Let $E$ be an encoding of a finite stack
machine $M$ with output stack $k_1$, $g$ symbol codes and stack numbering $\kappa$, let $\alpha$
be a symbol of stack $k_1$, and let $T, H, x \in \mathbb{N}$ with $x < g$. In the layout of $E$
at height $H$, let $C[t, k, j, z]$ be the variable for stack $k$, depth $j$ and symbol code $z$
at time $t$, and call a variable $v$ true under an assignment $a$ when $v < |a|$ and $a_v$ is
true. If an assignment $a$ satisfies the accept family for $\alpha$ at bounds $T$ and $H$, and
the variable $C[T, \kappa(k_1), 0, x]$ is true under $a$, then $x$ is the code of $\alpha$ for
stack $k_1$. -/
theorem acc_cell {acc : M.Γ M.k₁} {T H x : ℕ} {a : List Bool} (h : cnfSat (E.accFamily acc T H) a)
    (hx : x < E.g) (ht : Tr a (E.layout.cIdx H T (E.kc M.k₁) 0 x)) : x = E.enc M.k₁ acc :=
  of_decide_eq_true (unit_pol h (List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_range.2 hx,
      rfl⟩)) ht)

end Enc

/-- **Accepting configuration.** A configuration $c$ of a finite stack machine $M$ is accepting
for a symbol $\alpha$ of the output stack of $M$ when $c$ is halted (it has no label), its state
is the initial state of $M$, and the output stack of $c$ is nonempty with top symbol $\alpha$.

This is the shape of the halting configuration with output $[\alpha]$ that acceptance reads. -/
def Accepts (M : FinTM2) (c : M.Cfg) (acc : M.Γ M.k₁) : Prop :=
  c.l = none ∧ c.var = M.initialState ∧ (c.stk M.k₁).head? = some acc

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Satisfying assignments yield accepting runs.** Let $E$ be an encoding of a finite stack
machine $M$ with input stack $k_0$ and output stack $k_1$, let $x$ and $Y$ be lists of symbols of
$k_0$, let $m, T \in \mathbb{N}$ with $|x| \le m$, and let $\alpha$ be a symbol of $k_1$ that is one
of the effective symbols of $E$ for $k_1$. Put $H = m + (T + 1)d + 1$, where $d$ is the window
depth of $M$, and let $N$ be the number of situations of $E$. Suppose an assignment $a$ satisfies,
at bounds $T$ and $H$, the update family (the transition clause family of the layout of $E$ with
tables $\mathrm{la}, \mathrm{na}, \mathrm{wa}$ and $N$ situations), the S-definition family (the
same with $\mathrm{sa}$ in place of $\mathrm{na}$), the cell-shift family with tables
$\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ and $N$ situations, the init family for $x$,
$Y$ and $m$, and the accept family for $\alpha$. Then there is a list $y$ whose entries all occur
in $Y$ such that $|xy| \le m$ and the idle-extended run of $M$ from the initial configuration on
input $xy$ is, after $T$ steps, an accepting configuration for $\alpha$.

Apart from the accept family, no one-hot or at-most-one clauses are assumed. -/
theorem accept_sound {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁} {a : List Bool}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a)
    (hA : cnfSat (E.accFamily acc T (capH m T (depth M))) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc := by
  obtain ⟨y, hy, hl, hrow⟩ := E.rows_of_initFamily hx hu hs ha hI
  obtain ⟨hc, hr⟩ := hrow T le_rfl
  refine ⟨y, hy, hl, ?_⟩
  have hgood := E.run_good (x ++ y) T
  generalize runI M (initList M (x ++ y)) T = c at hc hr hgood
  have h1 : E.code c = E.acode := E.acc_code hA (E.lc_lt _) hc
  have h2 : (c.l, c.var) = ((none : Option M.Λ), M.initialState) := by
    have := congrArg E.ld h1
    simpa only [code, acode, E.ld_lc] using this
  obtain ⟨h2l, h2v⟩ := Prod.mk.inj h2
  have hH : 0 < capH m T (depth M) := by unfold capH; omega
  have h3 := E.acc_cell hA (E.cell_lt c hgood _ _) (hr _ (E.kc_lt M.k₁) 0 hH)
  rw [E.cell_kc] at h3
  obtain ⟨i, rfl⟩ := hacc
  refine ⟨h2l, h2v, ?_⟩
  rw [List.head?_eq_getElem?]
  cases hz : (c.stk M.k₁)[0]? with
  | none => rw [hz, E.enc_dec] at h3; simp at h3
  | some z =>
    rw [hz] at h3
    obtain ⟨n, rfl⟩ := hgood M.k₁ z (List.mem_of_getElem? hz)
    simp only [Option.elim, E.enc_dec, Nat.add_right_cancel_iff] at h3
    rw [Fin.ext h3]

/-- **No accepting certificate, no satisfying assignment.** Let $E$ be an encoding of a machine
$M$ with window depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let
$m, T \in \mathbb{N}$ with $|x| \le m$, let $H = m + (T + 1)d + 1$, and let $\alpha$ be a symbol
of the output stack of $M$ in the effective alphabet of $E$. Write
$\mathrm{la}, \mathrm{na}, \mathrm{sa}, \mathrm{wa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ for
the situation tables of $E$ and $N$ for its number of situations. Suppose that for no list $y$
of symbols, each in $Y$, with $|xy| \le m$, the configuration after $T$ steps of the
idle-extended run of $M$ from the initial configuration on input $xy$ is an accepting
configuration for $\alpha$. Then no assignment satisfies all five of the following families at
bounds $T$ and $H$: the transition clause family of the layout of $E$ for $N$ situations with
tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ (the update family); the transition clause
family for $N$ situations with tables $\mathrm{la}$, $\mathrm{sa}$, $\mathrm{wa}$ (the
S-definition family); the cell-shift clause family for $N$ situations with tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$; the init family of $E$ for $x$, $Y$, $m$; and the
accept family of $E$ for $\alpha$.

In particular, the all-true assignment does not satisfy all five. -/
theorem unsat_of_noAccept {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc)
    (hno : ¬ ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc) (a : List Bool) :
    ¬ (cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
      cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
      cnfSat (E.accFamily acc T (capH m T (depth M))) a) :=
  fun ⟨hu, hs, ha, hI, hA⟩ => hno (E.accept_sound hx hacc hu hs ha hI hA)

/-- **The all-true assignment satisfies the transition, shift and init families.** Let $E$ be an
encoding of a machine $M$ with window depth $d$, let $x$ and $Y$ be lists of symbols of the input
stack of $M$, and let $m, T, H \in \mathbb{N}$ with $|x| \le m < H$ and $d \le H$. Write
$\mathrm{la}, \mathrm{na}, \mathrm{sa}, \mathrm{wa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ for the
situation tables of $E$, $N$ for its number of situations and $V$ for the number of variables of
its layout at bounds $T$ and $H$. Then the all-true assignment of length $V$ satisfies each of the
following families at bounds $T$ and $H$: the transition clause family of the layout of $E$ for
$N$ situations with tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ (the update family); the
transition clause family for $N$ situations with tables $\mathrm{la}$, $\mathrm{sa}$,
$\mathrm{wa}$ (the S-definition family); the cell-shift clause family for $N$ situations with
tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$; and the init family of $E$ for
$x$, $Y$, $m$.

Every clause of these families has a positive literal at an index below $V$. -/
theorem trans_allTrue {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hx : x.length ≤ m) (hmH : m < H)
    (hH : depth M ≤ H) :
    cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) (List.replicate (E.layout.numVars T H) true) ∧
    cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) (List.replicate (E.layout.numVars T H) true) ∧
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) (List.replicate (E.layout.numVars T H) true) ∧
    cnfSat (E.initFamily x Ys m T H) (List.replicate (E.layout.numVars T H) true) :=
  ⟨(E.upd_pos hH).allTrue, (E.sdef_pos hH).allTrue, (E.shift_pos hH).allTrue,
    (E.init_pos hx hmH).allTrue⟩

theorem A0_two : 2 ≤ E.A0 := by
  have h1 := E.lc_lt (none, M.initialState)
  have h2 := E.lc_lt (some M.main, M.initialState)
  have hne : E.lc (none, M.initialState) ≠ E.lc (some M.main, M.initialState) := fun h => by
    have := congrArg E.ld h
    simp [E.ld_lc] at this
  omega

/-- **The all-true assignment violates the accept family.** Let $E$ be an encoding of a finite
stack machine $M$, let $\alpha$ be a symbol of the output stack of $M$, and let
$T, H \in \mathbb{N}$. The assignment that sets all $V$ variables to true, where $V$ is the number
of variables of the layout of $E$ at bounds $T$ and $H$, does not satisfy the accept family for
$\alpha$ at bounds $T$ and $H$. -/
theorem accFamily_allTrue (acc : M.Γ M.k₁) (T H : ℕ) :
    ¬ cnfSat (E.accFamily acc T H) (List.replicate (E.layout.numVars T H) true) := by
  intro h
  have hne : E.lc (some M.main, M.initialState) ≠ E.acode := fun h => by
    have := congrArg E.ld h
    simp [acode, E.ld_lc] at this
  have hlt := E.xIdx_lt (H := H) (le_refl T) (E.lc_lt (some M.main, M.initialState))
  refine hne (E.acc_code h (E.lc_lt _) ?_)
  unfold Tr
  rw [List.getElem?_replicate, ite_eq_left hlt]

end Enc


/-! ### Link to the repo's output notion (`EvalsTo`, `haltList`) -/

/-- **Unfolding the idle-extended run from the front.** For a finite TM2 machine $M$, a
configuration $c$ and every $n \in \mathbb{N}$, the configuration at time $n + 1$ of the
idle-extended run of $M$ from $c$ equals the configuration at time $n$ of the idle-extended run
of $M$ from the idle-extended step of $M$ at $c$. -/
theorem runI_succ' (M : FinTM2) (c : M.Cfg) : ∀ n, runI M c (n + 1) = runI M (stepI M c) n
  | 0 => rfl
  | n + 1 => by rw [runI, runI_succ' M c n]; rfl

theorem iterate_bind_none {σ : Type} (f : σ → Option σ) : ∀ n, (flip bind f)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iterate_bind_none f n

/-- **The idle-extended run follows the real run.** Let $M$ be a finite stack machine, let
$n \in \mathbb{N}$, and let $c, c'$ be configurations of $M$. If iterating the step function of
$M$ $n$ times as a partial function, starting from $c$, yields $c'$, then the idle-extended run
of $M$ from $c$ is at $c'$ after $n$ steps. -/
theorem runI_of_iterate (M : FinTM2) : ∀ (n : ℕ) (c c' : M.Cfg),
    (flip bind (TM2.step M.m))^[n] (some c) = some c' → runI M c n = c'
  | 0, c, c', h => Option.some.inj h
  | n + 1, c, c', h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind (TM2.step M.m))^[n] (TM2.step M.m c) = some c' at h
    cases hs : TM2.step M.m c with
    | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
    | some c1 =>
      rw [hs] at h
      rw [runI_succ', show stepI M c = c1 by simp [stepI, hs]; try rfl]
      exact runI_of_iterate M n c1 c' h

theorem runI_add (M : FinTM2) (c : M.Cfg) (a : ℕ) : ∀ b, runI M c (a + b) = runI M (runI M c a) b
  | 0 => rfl
  | b + 1 => by
    change stepI M (runI M c (a + b)) = stepI M (runI M (runI M c a) b)
    rw [runI_add M c a b]

/-- **A halted configuration is fixed by the idle-extended run.** Let $M$ be a finite stack
machine and $c$ a configuration of $M$ whose label is empty (that is, $c$ has halted). Then for
every $t \in \mathbb{N}$, the idle-extended run of $M$ from $c$ is at $c$ after $t$ steps. -/
theorem runI_halted (M : FinTM2) (c : M.Cfg) (hc : c.l = none) : ∀ t, runI M c t = c
  | 0 => rfl
  | t + 1 => by
    rw [runI, runI_halted M c hc t]
    obtain ⟨l, v, S⟩ := c
    subst hc
    simp [stepI, TM2.step]; try rfl

/-- **The idle-extended run stays at the halting configuration.** Let $M$ be a machine, $s$ a
word over its input alphabet and $l'$ a list over its output alphabet. Suppose that $M$, started
in the initial configuration on $s$, reaches the halting configuration with output $l'$ (halted,
in the initial state, with $l'$ on the output stack and every other stack empty) in at most $p$
steps. Then for every $T \ge p$, the configuration reached after $T$ steps of the idle-extended
run of $M$ from the initial configuration on $s$ is that halting configuration. -/
theorem runI_haltList (M : FinTM2) (s : List (M.Γ M.k₀)) (l' : List (M.Γ M.k₁)) {p : ℕ}
    (h : TM2OutputsInTime M s (some l') p) {T : ℕ} (hT : p ≤ T) :
    runI M (initList M s) T = haltList M l' := by
  have h1 := runI_of_iterate M h.steps _ _ h.evals_in_steps
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (h.steps_le_m.trans hT)
  rw [runI_add, h1, runI_halted _ _ rfl]

/-- **Acceptance of a halting configuration.** Let $M$ be a machine, $l'$ a list over its output
alphabet and $\mathrm{acc}$ an output symbol. The halting configuration with output $l'$ (halted,
in the initial state, with $l'$ on the output stack and every other stack empty) is accepting for
$\mathrm{acc}$ if and only if $l'$ is nonempty and its first element is $\mathrm{acc}$. -/
theorem accepts_haltList (M : FinTM2) (l' : List (M.Γ M.k₁)) (acc : M.Γ M.k₁) :
    Accepts M (haltList M l') acc ↔ l'.head? = some acc := by
  simp [Accepts, haltList]

/-! ### [C5] Completeness: the one-hot image of an accepting real run satisfies all five families
(2026-10-01, third). New ingredients vs. C6: index inversion (`row_pos_inj`, `Layout` injectivity)
and situation injectivity (`Enc.sit_inj`); clause semantics via `clauseSat_iff`. -/

/-- **Uniqueness of quotient and remainder.** Let $W$, $t$, $t'$, $r$ and $r'$ be natural
numbers with $r < W$ and $r' < W$. If $tW + r = t'W + r'$, then $t = t'$ and $r = r'$. -/
theorem row_pos_inj {W t t' r r' : ℕ} (hr : r < W) (hr' : r' < W)
    (h : t * W + r = t' * W + r') : t = t' ∧ r = r' := by
  have hW : 0 < W := by omega
  have e : ∀ t r, r < W → (t * W + r) / W = t := fun t r hr => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
  have ht : t = t' := by rw [← e t r hr, h, e t' r' hr']
  subst ht
  exact ⟨rfl, by omega⟩

section Inv

variable {L : Family.Layout}

theorem cIdx_split (H t k j x : ℕ) :
    L.cIdx H t k j x = t * L.rowW H + (L.A + ((k * H + j) * L.g + x)) := by
  unfold Family.Layout.cIdx; ring

theorem cell_off_lt {H k j x : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.A + ((k * H + j) * L.g + x) < L.rowW H := by
  have h1 : (k * H + j) * L.g + x < (k * H + j + 1) * L.g := by
    rw [Nat.add_one_mul]; omega
  have h2 : k * H + j + 1 ≤ L.KK * H := by
    have := Nat.mul_le_mul_right H (show k + 1 ≤ L.KK by omega)
    rw [Nat.add_one_mul] at this; omega
  have h3 := Nat.mul_le_mul_right L.g h2
  have e : L.KK * H * L.g = L.KK * (H * L.g) := by ring
  unfold Family.Layout.rowW; omega

theorem A_le_rowW (H : ℕ) : L.A ≤ L.rowW H := by unfold Family.Layout.rowW; omega

theorem xIdx_inj {H t t' u u' : ℕ} (hu : u < L.A) (hu' : u' < L.A)
    (h : L.xIdx H t u = L.xIdx H t' u') : t = t' ∧ u = u' :=
  row_pos_inj (lt_of_lt_of_le hu (A_le_rowW H)) (lt_of_lt_of_le hu' (A_le_rowW H)) h

theorem xIdx_ne_cIdx {H t t' u k j x : ℕ} (hu : u < L.A) (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.xIdx H t u ≠ L.cIdx H t' k j x := by
  intro h
  rw [cIdx_split] at h
  have := (row_pos_inj (lt_of_lt_of_le hu (A_le_rowW H)) (cell_off_lt hk hj hx) h).2
  omega

theorem cIdx_inj {H t t' k k' j j' x x' : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g)
    (hk' : k' < L.KK) (hj' : j' < H) (hx' : x' < L.g)
    (h : L.cIdx H t k j x = L.cIdx H t' k' j' x') : t = t' ∧ k = k' ∧ j = j' ∧ x = x' := by
  rw [cIdx_split, cIdx_split] at h
  obtain ⟨rfl, h⟩ := row_pos_inj (cell_off_lt hk hj hx) (cell_off_lt hk' hj' hx') h
  obtain ⟨h1, rfl⟩ := row_pos_inj (t := k * H + j) (t' := k' * H + j') hx hx' (by omega)
  obtain ⟨rfl, rfl⟩ := row_pos_inj hj hj' h1
  exact ⟨rfl, rfl, rfl, rfl⟩

end Inv

/-- **Equal low-order digits give equal residues.** Let $b$, $i$, $i'$ and $n$ be natural
numbers. If $\lfloor i / b^e \rfloor \bmod b = \lfloor i' / b^e \rfloor \bmod b$ for every
$e < n$, that is, $i$ and $i'$ have the same first $n$ base-$b$ digits, then
$i \bmod b^n = i' \bmod b^n$. -/
theorem mod_pow_eq_of_digits {b i i' : ℕ} : ∀ n, (∀ e < n, i / b ^ e % b = i' / b ^ e % b) →
    i % b ^ n = i' % b ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, mod_pow_eq_of_digits n fun e he => h e (by omega),
      h n (by omega)]

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Situation injectivity.** Let $M$ be a finite stack machine with encoding data $E$, and write
$N$ for the number of situations of $E$, $K$ for the number of stacks of $E$ and $d$ for the
window depth of $M$. Let $c$ be a configuration of $M$ all of whose stack symbols lie in the
effective alphabets of $E$, and let $i < N$. If the label/state code of situation $i$ equals the
(label, state) code of $c$, and for every stack number $k < K$ and every depth $j < d$ the window
code of situation $i$ at stack $k$, depth $j$ equals the cell code of $c$ at stack $k$, depth
$j$, then $i$ is the situation index of $c$.

This is the converse of the fact that the situation index of such a $c$ is below $N$ and has the
code and the windows of $c$. -/
theorem sit_inj (c : M.Cfg) (hc : E.Good c) {i : ℕ} (hi : i < E.N) (hl : E.la i = E.code c)
    (hw : ∀ k < E.KK, ∀ j < depth M, E.wa i k j = E.cell c k j) : i = E.sitIdx c := by
  obtain ⟨hN, hl', hw'⟩ := E.sitIdx_spec c hc
  set i' := E.sitIdx c
  have hG : 0 < E.G := pow_pos E.g_pos _
  have top : ∀ n, n < E.N → E.la n = n / E.G := fun n hn => by
    unfold la
    exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hG).2 hn)
  have hdig : ∀ e < E.KK * depth M, i / E.g ^ e % E.g = i' / E.g ^ e % E.g := by
    intro e he
    have hd : 0 < depth M := Nat.pos_of_ne_zero fun h => by simp [h] at he
    have hk : e / depth M < E.KK := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
    have hj : e % depth M < depth M := Nat.mod_lt _ hd
    have h1 := hw _ hk _ hj
    have h2 := hw' _ hk _ hj
    unfold wa at h1 h2
    rw [Nat.div_add_mod'] at h1 h2
    rw [h1, h2]
  have hmod := mod_pow_eq_of_digits (b := E.g) (i := i) (i' := i') _ hdig
  have hdiv : i / E.G = i' / E.G := by rw [← top i hi, ← top i' hN, hl, hl']
  rw [← Nat.mod_add_div i E.G, ← Nat.mod_add_div i' E.G]
  unfold G at hdiv ⊢
  rw [hmod, hdiv]

/-! #### The assignment: the exact one-hot image of the real run -/

/-- **The real run's literals.** Let $M$ be a finite stack machine with encoding data $E$, let $s$
be an input of $M$ and $H \in \mathbb{N}$, and for $t \in \mathbb{N}$ let $c_t$ be the
configuration after $t$ steps of the idle-extended run of $M$ from its start configuration on $s$.
Variable indices are those of the layout of $E$ at height $H$, $K$ is the number of stacks of $E$,
and $A_0$ is the number of (label, state) codes of $E$. An index $p$ is a run literal when, for
some time $t$, it is one of the following: the label/state variable at time $t$ for the
(label, state) code of $c_t$; for some stack number $k < K$ and depth $j < H$, the cell variable
at time $t$ for stack $k$, depth $j$ and the cell code of $c_t$ at stack $k$, depth $j$ (code $0$,
the empty cell, included); or the label/state variable at time $t + 1$ for $A_0 + i$, where $i$
is the situation index of $c_t$. -/
def RunLit (s : List (M.Γ M.k₀)) (H p : ℕ) : Prop :=
  ∃ t, p = E.layout.xIdx H t (E.code (runI M (initList M s) t)) ∨
    (∃ k < E.KK, ∃ j < H, p = E.layout.cIdx H t k j (E.cell (runI M (initList M s) t) k j)) ∨
    p = E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))

open Classical in
/-- **The assignment of the real run's literals.** Let $E$ be an encoding of the machine $M$, let
$s$ be a word over the input alphabet, let $T$ and $H$ be natural numbers, and let $V$ be the
number of variables of the transition-clause formula for $T$ and $H$. The assignment is the list
of $V$ truth values whose entry $p$, for each $p < V$, is true exactly when $p$ is one of the
real run's literals of $s$ at height $H$. -/
noncomputable def runAsg (s : List (M.Γ M.k₀)) (T H : ℕ) : List Bool :=
  (List.range (E.layout.numVars T H)).map fun p => decide (E.RunLit s H p)

theorem runAsg_length (s : List (M.Γ M.k₀)) (T H : ℕ) :
    (E.runAsg s T H).length = E.layout.numVars T H := by
  simp [runAsg]

theorem runAsg_get {s : List (M.Γ M.k₀)} {T H p : ℕ} (hp : p < E.layout.numVars T H) (b : Bool)
    (hb : b = true ↔ E.RunLit s H p) : (E.runAsg s T H)[p]? = some b := by
  unfold runAsg
  rw [List.getElem?_map, List.getElem?_range hp]
  cases b <;> simp_all

/-- **Faithful clauses with a literal agreeing with the real run are satisfied.** Let $M$ be a
finite stack machine with encoding data $E$, let $s$ be an input of $M$, let
$T, H \in \mathbb{N}$, and let $V$ be the number of variables of the layout of $E$ for $T$ and
$H$. Let $\ell$ be a list of literals that is faithful for $V$, and let $(p, b) \in \ell$ be a
literal such that $b$ is true exactly when $p$ is a run literal of $s$ at height $H$. Then the
dense clause over $V$ variables built from $\ell$ is satisfied by the run assignment of $s$ for
$T$ and $H$, which is true exactly on the run literals. -/
theorem sat_run {s : List (M.Γ M.k₀)} {T H : ℕ} {ls : List (ℕ × Bool)}
    (hf : Faithful (E.layout.numVars T H) ls) {p : ℕ} {b : Bool} (hp : (p, b) ∈ ls)
    (hb : b = true ↔ E.RunLit s H p) :
    clauseSat (Family.denseClause (E.layout.numVars T H) ls) (E.runAsg s T H) :=
  (clauseSat_iff hf).2 ⟨p, b, hp, E.runAsg_get (hf p b hp).1 b hb⟩

/-! #### `RunLit` read back (index inversion) -/

/-- **Situation variables lie in the label/state block.** Let $E$ be an encoding of a finite TM2
machine with $N$ situations. For every natural number $i < N$, the position of the variable of
situation $i$ is less than the label/state block size $A$ of the clause layout of $E$. -/
theorem sa_lt {i : ℕ} (hi : i < E.N) : E.sa i < E.layout.A := by
  change E.A0 + i < E.A0 + E.N; omega

theorem code_lt (c : M.Cfg) : E.code c < E.layout.A := by
  have := E.lc_lt (c.l, c.var); show _ < E.A0 + E.N; unfold code; omega

theorem lit_x (s : List (M.Γ M.k₀)) {H t u : ℕ} (hu : u < E.A0) :
    E.RunLit s H (E.layout.xIdx H t u) ↔ u = E.code (runI M (initList M s) t) := by
  have hu' : u < E.layout.A := by show u < E.A0 + E.N; omega
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inl (by rw [h])⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k, hk, j, hj, h⟩ | h
  · obtain ⟨rfl, rfl⟩ := xIdx_inj hu' (E.code_lt _) h; rfl
  · exact absurd h (xIdx_ne_cIdx hu' hk hj (E.cell_lt _ hg k j))
  · have := (xIdx_inj hu' (E.sa_lt (E.sitIdx_spec _ hg).1) h).2
    unfold sa at this; omega

theorem lit_c (s : List (M.Γ M.k₀)) {H t k j x : ℕ} (hk : k < E.KK) (hj : j < H) (hx : x < E.g) :
    E.RunLit s H (E.layout.cIdx H t k j x) ↔ x = E.cell (runI M (initList M s) t) k j := by
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inr (Or.inl ⟨k, hk, j, hj, by rw [h]⟩)⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k', hk', j', hj', h⟩ | h
  · exact absurd h.symm (xIdx_ne_cIdx (E.code_lt _) hk hj hx)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := cIdx_inj hk hj hx hk' hj' (E.cell_lt _ hg k' j') h; rfl
  · exact absurd h.symm (xIdx_ne_cIdx (E.sa_lt (E.sitIdx_spec _ hg).1) hk hj hx)

theorem lit_s (s : List (M.Γ M.k₀)) {H t i : ℕ} (hi : i < E.N) :
    E.RunLit s H (E.layout.xIdx H (t + 1) (E.sa i)) ↔ i = E.sitIdx (runI M (initList M s) t) := by
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inr (Or.inr (by rw [h]))⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k, hk, j, hj, h⟩ | h
  · have := (xIdx_inj (E.sa_lt hi) (E.code_lt _) h).2
    have := E.lc_lt ((runI M (initList M s) t').l, (runI M (initList M s) t').var)
    unfold sa code at *; omega
  · exact absurd h (xIdx_ne_cIdx (E.sa_lt hi) hk hj (E.cell_lt _ hg k j))
  · obtain ⟨h1, h2⟩ := xIdx_inj (E.sa_lt hi) (E.sa_lt (E.sitIdx_spec _ hg).1) h
    obtain rfl : t = t' := by omega
    unfold sa at h2; omega

/-! #### Family by family -/

/-- **Transition families with a run-literal head are satisfied by the run.** Let $E$ be an
encoding of the machine $M$ with layout $L$, $N$ situations, label/state table $\mathrm{la}$ and
window table $\mathrm{wa}$, let $d$ be the window depth of $M$, and let $T, H \in \mathbb{N}$ with
$d \le H$. Write $X[r, x]$ for the index of the label/state variable $x$ of row $r$ at height
$H$. Fix an input list $s$, let $c_t$ be the configuration after $t$ steps of the idle-extended
run of $M$ from the initial configuration on $s$, and let $\nu : \mathbb{N} \to \mathbb{N}$ be a
next-label table such that $\mathrm{la}$, $\nu$ and $\mathrm{wa}$ are well formed for $L$ at
height $H$ for every situation $i < N$. Suppose that for every $t < T$, with $i_t$ the situation
index of $c_t$, the index $X[t + 1, \nu(i_t)]$ is one of the real run's literals of $s$ at
height $H$. Then the assignment of the real run's literals of $s$ for $T$ and $H$ satisfies the
transition clause family of $L$ with the tables $\mathrm{la}$, $\nu$ and $\mathrm{wa}$ for $T$,
$H$ and $N$.

In clause $(t, i)$ the head literal is true when $i$ is the situation index of $c_t$; otherwise
the clause is satisfied by a body literal whose variable is false, by situation injectivity. -/
theorem fam_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (nx : ℕ → ℕ)
    (hwf : ∀ i < E.N, Family.WF E.layout E.la nx E.wa H i) (hdH : depth M ≤ H)
    (hnx : ∀ t < T,
        E.RunLit s H (E.layout.xIdx H (t + 1) (nx (E.sitIdx (runI M (initList M s) t))))) :
    cnfSat (Family.family E.layout E.la nx E.wa T H E.N) (E.runAsg s T H) := by
  intro c hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_range] at ht hi
  have hf := faithful_of_inc (Family.lits_inc ht (hwf i hi))
  have hn : E.layout.nLits = E.KK * depth M + 2 := rfl
  have mem : ∀ j < E.layout.nLits, (Family.litPos E.layout E.la nx E.wa H t i j,
      decide (j = E.layout.nLits - 1)) ∈ Family.lits E.layout E.la nx E.wa H t i :=
    fun j hj => List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  set c := runI M (initList M s) t with hc
  by_cases hsit : i = E.sitIdx c
  · refine E.sat_run hf (mem (E.layout.nLits - 1) (by omega)) ?_
    have : Family.litPos E.layout E.la nx E.wa H t i (E.layout.nLits - 1) =
        E.layout.xIdx H (t + 1) (nx i) := by
      unfold Family.litPos; rw [ite_eq_right (by omega),
          ite_eq_right (show ¬ _ ≤ E.layout.KK * E.layout.d by
        change ¬ _ ≤ E.KK * depth M; omega)]
    rw [this, hsit]; simpa using hnx t ht
  by_cases hla : E.la i = E.code c
  · have : ∃ k < E.KK, ∃ j < depth M, E.wa i k j ≠ E.cell c k j := by
      by_contra hno
      push Not at hno
      exact hsit (E.sit_inj c (E.run_good s t) hi hla hno)
    obtain ⟨k, hk, j, hj, hne⟩ := this
    have hkj : k * depth M + j < E.KK * depth M := by
      have := Nat.mul_le_mul_right (depth M) (show k + 1 ≤ E.KK by omega)
      rw [Nat.add_one_mul] at this; omega
    refine E.sat_run hf (mem (k * depth M + j + 1) (by omega)) ?_
    have hd : 0 < depth M := by omega
    have e1 : (k * depth M + j) / depth M = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (k * depth M + j) % depth M = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have : Family.litPos E.layout E.la nx E.wa H t i (k * depth M + j + 1) =
        E.layout.cIdx H t k j (E.wa i k j) := by
      unfold Family.litPos
      rw [ite_eq_right (by omega), ite_eq_left (show _ ≤ E.layout.KK * E.layout.d from
        show _ ≤ E.KK * depth M by omega)]
      change E.layout.cIdx H t ((k * depth M + j + 1 - 1) / depth M) ((k * depth M + j + 1 - 1) % depth M)
        (E.wa i ((k * depth M + j + 1 - 1) / depth M) ((k * depth M + j + 1 - 1) % depth M)) = _
      rw [Nat.add_sub_cancel, e1, e2]
    rw [this, E.lit_c s hk (by omega) (E.wa_lt i k j)]
    simp only [show k * depth M + j + 1 ≠ E.layout.nLits - 1 by omega, decide_false]
    simpa using hne
  · refine E.sat_run hf (mem 0 (by omega)) ?_
    have : Family.litPos E.layout E.la nx E.wa H t i 0 = E.layout.xIdx H t (E.la i) := by
      unfold Family.litPos; rw [ite_eq_left rfl]
    rw [this, E.lit_x s (E.la_lt i)]
    simp only [show (0 : ℕ) ≠ E.layout.nLits - 1 by omega, decide_false]
    simpa using hla

/-- **The run assignment satisfies the update family.** Let $M$ be a finite stack machine with
encoding data $E$, let $N$ be the number of situations of $E$, let $s$ be an input of $M$, and
let $T, H \in \mathbb{N}$ with $d \le H$, where $d$ is the window depth of $M$. For
$t \in \mathbb{N}$ let $c_t$ be the configuration after $t$ steps of the idle-extended run of $M$
from its start configuration on $s$, and suppose that for every $t < T$ every stack of $c_t$ has
length at most $H - d$. Then the run assignment of $s$ for $T$ and $H$ (true exactly on the run
literals) satisfies the transition clause family of the layout of $E$ at height $H$, for times
$t < T$ and situations $i < N$, with the tables $\mathrm{la}$, $\mathrm{na}$ and $\mathrm{wa}$
of $E$.

In the clause of the real situation, the head literal is the code of the real next
configuration, by the agreement of the tables with the machine's step. -/
theorem upd_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) (E.runAsg s T H) :=
  E.fam_complete s E.na (fun i _ => E.wf_upd hdH i) hdH fun t ht =>
    ⟨t + 1, Or.inl (by rw [(E.table_agree_run H s t (hh t ht)).2.2.2.1])⟩

/-- **The run assignment satisfies the situation-definition family.** Let $M$ be a finite stack
machine with encoding data $E$, let $N$ be the number of situations of $E$, let $s$ be an input
of $M$, and let $T, H \in \mathbb{N}$ with $d \le H$, where $d$ is the window depth of $M$. Then
the run assignment of $s$ for $T$ and $H$ (true exactly on the run literals) satisfies the
transition clause family of the layout of $E$ at height $H$, for times $t < T$ and situations
$i < N$, with the tables $\mathrm{la}$ and $\mathrm{wa}$ of $E$ and with the situation positions
$\mathrm{sa}$ of $E$ in place of the next-label table.

In the clause of the real situation, the head literal is the real situation literal, by the
definition of the run literals. -/
theorem sdef_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H) :
    cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) (E.runAsg s T H) :=
  E.fam_complete s E.sa (fun i hi => E.wf_sdef hdH i hi) hdH fun t _ =>
    ⟨t, Or.inr (Or.inr rfl)⟩

/-- **The run assignment satisfies the cell-shift family.** Let $M$ be a finite stack machine
with encoding data $E$, let $N$ be the number of situations of $E$, let $s$ be an input of $M$,
and let $T, H \in \mathbb{N}$ with $d \le H$, where $d$ is the window depth of $M$. For
$t \in \mathbb{N}$ let $c_t$ be the configuration after $t$ steps of the idle-extended run of $M$
from its start configuration on $s$, and suppose that for every $t < T$ every stack of $c_t$ has
length at most $H - d$. Then the run assignment of $s$ for $T$ and $H$ (true exactly on the run
literals) satisfies the cell-shift clause family (shift, overflow and pushed-fill clauses) of the
layout of $E$ with the tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ of $E$,
for $N$ situations, times $t < T$ and height $H$.

Off the real situation the negated situation literal is true; on it, the target cell of row
$t + 1$ is the one given by the table-driven row update. -/
theorem shift_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) (E.runAsg s T H) := by
  have hwf := E.wf_sh hdH
  intro c hc
  simp only [Shift.shFamily, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨t, ht, i, hi, k, hk, hc⟩ := hc
  obtain ⟨-, -, -, -, hrow⟩ := E.table_agree_run H s t (hh t ht)
  have hS := E.lit_s s (H := H) (t := t) hi
  set c := runI M (initList M s) t with hcdef
  have hpl := E.pl_le i k
  have hcn := E.cn_le i k
  simp only [Shift.shBlk, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with (⟨u, hu, x, hx, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨j, hj, rfl⟩
  · have := Shift.inc_drop (cl := (.sh ⟨x, hx⟩ : Shift.CL E.layout.g E.layout.d))
      (Shift.shPos_mono (i := ⟨i, hi⟩) (k := ⟨k,
          hk⟩) ht hwf (Nat.add_lt_of_lt_sub hu) hx) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_sh] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      by_cases hxc : x = E.cell c k (u + E.cn (E.sitIdx c) k)
      · refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k (u + E.pl (E.sitIdx c) k) x) (b := true)
          (by simp [Shift.shLits]) ?_
        rw [E.lit_c s hk (by omega) hx, hrow k hk _ (by omega)]
        unfold tabRow
        rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel, ← hxc]
        simp
      · refine E.sat_run hf (p := E.layout.cIdx H t k (u + E.cn (E.sitIdx c) k) x) (b := false)
          (by simp [Shift.shLits]) ?_
        rw [E.lit_c s hk (by omega) hx]
        simpa using hxc
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.shLits]) (by rw [hS]; simpa using hsit)
  · have := Shift.inc_drop (cl := (.ov : Shift.CL E.layout.g E.layout.d))
      (Shift.ovPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hr) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_ov] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k + r) 0)
        (b := true) (by simp [Shift.ovLits]) ?_
      rw [E.lit_c s hk (by omega) E.g_pos, hrow k hk _ (by omega)]
      unfold tabRow
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.ovLits]) (by rw [hS]; simpa using hsit)
  · have hjd : j < E.layout.d := lt_of_lt_of_le hj (hwf.pl_le i hi k hk)
    have := Shift.inc_drop (cl := (.pf ⟨j, hjd⟩ : Shift.CL E.layout.g E.layout.d))
      (Shift.pfPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hj) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_pf] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k j (E.pu (E.sitIdx c) k j)) (b := true)
        (by simp [Shift.pfLits]) ?_
      rw [E.lit_c s hk (by omega) (E.pu_lt _ k j hj), hrow k hk _ (by omega)]
      unfold tabRow
      rw [ite_eq_left hj]
      simp
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.pfLits]) (by rw [hS]; simpa using hsit)


/-- **Unit clauses on run literals are satisfied.** Let $M$ be a finite stack machine with
encoding data $E$, let $s$ be an input of $M$, let $T, H \in \mathbb{N}$, and let $V$ be the
number of variables of the layout of $E$ for $T$ and $H$. If $p < V$ is a run literal of $s$ at
height $H$, then the dense clause over $V$ variables whose only literal is $x_p$ is satisfied by
the run assignment of $s$ for $T$ and $H$, which is true exactly on the run literals. -/
theorem sat_unit {s : List (M.Γ M.k₀)} {T H p : ℕ} (hp : p < E.layout.numVars T H)
    (h : E.RunLit s H p) :
    clauseSat (Family.denseClause (E.layout.numVars T H) [(p, true)]) (E.runAsg s T H) :=
  E.sat_run (faithful_single hp) (List.mem_singleton.2 rfl) (iff_of_true rfl h)

/-- **Row-0 cells of the start configuration are run literals.** Let $E$ be an encoding of the
machine $M$ with $K$ stacks, let $s$ be a word over the input alphabet, and let $H$, $k$ and $j$
be natural numbers with $k < K$ and $j < H$. Let $x$ be the code of the cell of stack $k$ at
depth $j$ in the initial configuration on $s$. Then the cell variable of time $0$, stack $k$,
depth $j$ and symbol code $x$ at height $H$ is one of the real run's literals of $s$ at
height $H$. -/
theorem lit_cell0 (s : List (M.Γ M.k₀)) {H k j : ℕ} (hk : k < E.KK) (hj : j < H) :
    E.RunLit s H (E.layout.cIdx H 0 k j (E.cell (initList M s) k j)) :=
  ⟨0, Or.inr (Or.inl ⟨k, hk, j, hj, rfl⟩)⟩

theorem cell0_k₀ (s : List (M.Γ M.k₀)) (j : ℕ) :
    E.cell (initList M s) (E.kc M.k₀) j = (s[j]?).elim 0 (E.enc M.k₀) := by
  rw [E.cell_kc, initList_k₀]

/-- **Completeness of the init family.** Let $E$ be an encoding of the machine $M$, let $x$, $y$
and $Y$ be words over the input alphabet such that every letter of $y$ occurs in $Y$, and let
$m$, $T$ and $H$ be natural numbers with $|xy| \le m < H$, where $xy$ is the concatenation. Then
the assignment of the real run's literals of $xy$ for $T$ steps at height $H$ satisfies the init
family (clauses I1 to I6) for $x$, $Y$, $m$, $T$ and $H$. -/
theorem init_complete {x y Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hy : ∀ z ∈ y, z ∈ Ys)
    (hl : (x ++ y).length ≤ m) (hmH : m < H) :
    cnfSat (E.initFamily x Ys m T H) (E.runAsg (x ++ y) T H) := by
  have cl : ∀ k j v, k < E.KK → j < H → v < E.g → E.layout.cIdx H 0 k j v < E.layout.numVars T H :=
    fun k j v hk hj hv => E.cIdx_lt (Nat.zero_le T) hk hj hv
  have e0 : ∀ z : M.Γ M.k₀, E.enc M.k₀ z < E.g := fun z => E.enc_lt _ z (E.input_mem z)
  have hk0 := E.kc_lt M.k₀
  have hxl : x.length ≤ (x ++ y).length := by simp
  -- the input-stack cell at depth `j` is `⊥` iff `j ≥ |x ++ y|`
  have z0 : ∀ j, (x ++ y).length ≤ j → E.cell (initList M (x ++ y)) (E.kc M.k₀) j = 0 := by
    intro j hj; rw [E.cell0_k₀, List.getElem?_eq_none hj]; rfl
  have z1 : ∀ j, j < (x ++ y).length → E.cell (initList M (x ++ y)) (E.kc M.k₀) j ≠ 0 := by
    intro j hj
    rw [E.cell0_k₀, List.getElem?_eq_getElem hj, Option.elim_some]
    obtain ⟨n, hn⟩ := E.input_mem (x ++ y)[j]
    rw [← hn, E.enc_dec]; omega
  simp only [initFamily, cnfSat_append]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- I1
    intro c hc
    obtain rfl := List.mem_singleton.1 hc
    exact E.sat_unit (E.xIdx_lt (Nat.zero_le T) (E.lc_lt _)) ⟨0, Or.inl rfl⟩
  · -- I2
    intro c hc
    obtain ⟨k, hk, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    obtain ⟨hk, hne⟩ := List.mem_filter.1 hk
    rw [List.mem_range] at hk hj
    have hne : E.kd k ≠ M.k₀ := fun h => by
      have := E.kc_kd k hk; rw [h] at this; simp [this] at hne
    have h0 : E.cell (initList M (x ++ y)) k j = 0 := by
      unfold cell; rw [initList_ne _ _ hne]; rfl
    refine E.sat_unit (cl _ _ _ hk hj E.g_pos) ?_
    have := E.lit_cell0 (x ++ y) hk hj
    rwa [h0] at this
  · -- I3
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hj
    have hjH : j < H := by omega
    refine E.sat_unit (cl _ _ _ hk0 hjH (by rw [List.getElem?_eq_getElem hj]; exact e0 _)) ?_
    have := E.lit_cell0 (x ++ y) hk0 hjH
    rwa [E.cell0_k₀, List.getElem?_append_left hj] at this
  · -- I4
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    have hjH : x.length + i < H := by omega
    have hf : Faithful (E.layout.numVars T H) ((E.zIdx H (x.length + i), true) ::
        Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true)) := by
      refine faithful_pos fun p b hp => ?_
      rcases List.mem_cons.1 hp with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨cl _ _ _ hk0 hjH E.g_pos, rfl⟩
      · obtain ⟨z, _, he⟩ := List.mem_map.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨cl _ _ _ hk0 hjH (e0 z), rfl⟩
    have hlit := E.lit_cell0 (x ++ y) hk0 hjH
    by_cases hin : x.length + i < (x ++ y).length
    · have hiy : i < y.length := by simp at hin; omega
      refine E.sat_run hf (p := E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ y[i]))
        (b := true) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hy _ (List.getElem_mem hiy), rfl⟩))
        (iff_of_true rfl ?_)
      rwa [E.cell0_k₀, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hiy, Option.elim_some] at hlit
    · refine E.sat_run hf (p := E.zIdx H (x.length + i)) (b := true) List.mem_cons_self
        (iff_of_true rfl ?_)
      unfold zIdx
      rwa [z0 _ (by omega)] at hlit
  · -- I5
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    have h2 := cl (E.kc M.k₀) (x.length + i + 1) 0 hk0 (by omega) E.g_pos
    have hg := E.g_pos
    have h1 : E.zIdx H (x.length + i) + 1 ≤ E.zIdx H (x.length + i + 1) := by
      unfold zIdx Family.Layout.cIdx
      have : (E.kc M.k₀ * H + (x.length + i + 1)) * E.layout.g =
          (E.kc M.k₀ * H + (x.length + i)) * E.layout.g + E.layout.g := by ring
      have : E.layout.g = E.g := rfl
      omega
    have hf := faithful_of_inc (lo := 0) (V := E.layout.numVars T H)
      (ls := [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1), true)])
      ⟨Nat.zero_le _, h1, h2⟩
    by_cases hin : x.length + i < (x ++ y).length
    · refine E.sat_run hf (p := E.zIdx H (x.length + i)) (b := false) List.mem_cons_self ?_
      unfold zIdx
      rw [E.lit_c _ hk0 (by omega) E.g_pos]
      simpa [runI] using (z1 _ hin).symm
    · refine E.sat_run hf (p := E.zIdx H (x.length + i + 1)) (b := true)
        (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) (iff_of_true rfl ?_)
      have := E.lit_cell0 (x ++ y) hk0 (show x.length + i + 1 < H by omega)
      unfold zIdx
      rwa [z0 _ (by omega)] at this
  · -- I6
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    refine E.sat_unit (cl _ _ _ hk0 (by omega) E.g_pos) ?_
    have := E.lit_cell0 (x ++ y) hk0 (show m + i < H by omega)
    unfold zIdx
    rwa [z0 _ (by omega)] at this

/-- **Completeness of the accept family.** Let $E$ be an encoding of the machine $M$, let $s$ be
a word over the input alphabet, let $T$ and $H$ be natural numbers with $H > 0$, and let
$\mathrm{acc}$ be a symbol of the output stack. Suppose that the configuration reached after $T$
steps of the idle-extended run of $M$ from the initial configuration on $s$ is accepting for
$\mathrm{acc}$: it is halted, its state is the initial state of $M$, and $\mathrm{acc}$ is on top
of its output stack. Then the assignment of the real run's literals of $s$ for $T$ steps at
height $H$ satisfies the accept family for $\mathrm{acc}$ at $T$ and $H$, both its positive and
its negated unit clauses. -/
theorem acc_complete (s : List (M.Γ M.k₀)) {T H : ℕ} {acc : M.Γ M.k₁} (hH : 0 < H)
    (hA : Accepts M (runI M (initList M s) T) acc) :
    cnfSat (E.accFamily acc T H) (E.runAsg s T H) := by
  obtain ⟨hl, hv, hk⟩ := hA
  have hcode : E.code (runI M (initList M s) T) = E.acode := by
    unfold code acode; rw [hl, hv]
  have hcell : E.cell (runI M (initList M s) T) (E.kc M.k₁) 0 = E.enc M.k₁ acc := by
    rw [E.cell_kc, ← List.head?_eq_getElem?, hk]; rfl
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hu
    refine E.sat_run (faithful_single (E.xIdx_lt le_rfl hu)) (List.mem_singleton.2 rfl) ?_
    rw [E.lit_x s hu, hcode]; simp
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hx
    refine E.sat_run (faithful_single (E.cIdx_lt le_rfl (E.kc_lt _) hH hx))
      (List.mem_singleton.2 rfl) ?_
    rw [E.lit_c s (E.kc_lt _) hH hx, hcell]; simp

/-- **Completeness of the five clause families.** Let $E$ be an encoding of the machine $M$, let
$x$, $y$ and $Y$ be words over the input alphabet such that every letter of $y$ occurs in $Y$, and
let $m$ and $T$ be natural numbers with $|xy| \le m$, where $xy$ is the concatenation. Let $d$ be
the window depth of $M$, let $H = m + (T + 1)d + 1$ be the stack cap, and let $a$ be the
assignment of the real run's literals of $xy$ for $T$ steps at height $H$. Suppose that the
configuration reached after $T$ steps of the idle-extended run of $M$ from the initial
configuration on $xy$ is accepting for the output symbol $\mathrm{acc}$: it is halted, its state
is the initial state of $M$, and $\mathrm{acc}$ is on top of its output stack. Then the length of
$a$ is the number of variables of the transition-clause formula for $T$ and $H$, and $a$
satisfies each of the following, all for $T$ steps at height $H$: the update family (the
transition clause family with tables $\mathrm{la}$, $\mathrm{na}$, $\mathrm{wa}$ and $N$
situations), the S-definition family (the transition clause family with tables $\mathrm{la}$,
$\mathrm{sa}$, $\mathrm{wa}$ and $N$ situations), the cell-shift family with tables
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations, the init family for
$x$, $Y$ and $m$, and the accept family for $\mathrm{acc}$.

No bound $|x| \le m$ and no encodability of $\mathrm{acc}$ is needed in this direction. -/
theorem accept_complete {x y Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hy : ∀ z ∈ y, z ∈ Ys) (hl : (x ++ y).length ≤ m)
    (hA : Accepts M (runI M (initList M (x ++ y)) T) acc) :
    let a := E.runAsg (x ++ y) T (capH m T (depth M))
    a.length = E.layout.numVars T (capH m T (depth M)) ∧
    cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
    cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
    cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
    cnfSat (E.accFamily acc T (capH m T (depth M))) a := by
  have hh : ∀ t < T, ∀ k, ((runI M (initList M (x ++ y)) t).stk k).length ≤
      capH m T (depth M) - depth M := fun t ht k => capH_height (x ++ y) hl ht.le k
  have hdH := depth_le_capH M m T
  exact ⟨E.runAsg_length _ _ _, E.upd_complete _ hdH hh, E.sdef_complete _ hdH,
    E.shift_complete _ hdH hh, E.init_complete hy hl (by unfold capH; omega),
    E.acc_complete _ (by unfold capH; omega) hA⟩

/-- **The five Cook–Levin clause families are satisfiable iff some certificate is accepted.**
Let $E$ be an encoding of the multi-stack machine $M$, with input stack $k_0$, output stack
$k_1$ and window depth $d$. Let $x$ and $Y$ be lists of input symbols, let $m, T \in \mathbb{N}$,
let $\mathrm{acc}$ be an output symbol, and let $H = m + (T + 1)d + 1$ be the stack cap. Suppose
$|x| \le m$ and $\mathrm{acc}$ is one of the effective symbols that $E$ fixes for stack $k_1$.
Then some list $a$ of Booleans satisfies all five of the following CNF formulas, each for $T$
steps and cap $H$: the transition family with tables $\mathrm{la}, \mathrm{na}, \mathrm{wa}$ and
the transition family with tables $\mathrm{la}, \mathrm{sa}, \mathrm{wa}$, both over the layout
of $E$ and its $N$ situations; the cell-shift family over the same layout with tables
$\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ and $N$ situations; the init family for $x$,
$Y$ and $m$; and the accept family for $\mathrm{acc}$, if and only if there is a list $y$ of
input symbols, all in $Y$, with $|xy| \le m$ such that the idle-extended run of $M$ from the
initial configuration on input $xy$ is, after $T$ steps, an accepting configuration for
$\mathrm{acc}$: halted, in the initial state, with $\mathrm{acc}$ on top of stack $k_1$. -/
theorem five_iff {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc) :
    (∃ a : List Bool,
      cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
      cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
      cnfSat (E.accFamily acc T (capH m T (depth M))) a) ↔
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc := by
  constructor
  · rintro ⟨a, hu, hs, ha, hI, hA⟩
    exact E.accept_sound hx hacc hu hs ha hI hA
  · rintro ⟨y, hy, hl, hA⟩
    obtain ⟨_, h⟩ := E.accept_complete hy hl hA
    exact ⟨_, h⟩

end Enc

end C6

end Cslib.Complexity.CookLevin.Situation
