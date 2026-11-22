/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.HMM.PairHMM
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Profile hidden Markov models

A profile HMM (Krogh, Brown, Mian, Sjölander and Haussler 1994; Eddy 1998; Durbin et al. 1998,
chapter 5) models a protein or DNA family by `L` consensus columns. Node `k` (`1 ≤ k ≤ L`) has a
match state `M k` (emits a residue aligned to column `k`), a delete state `D k` (silent: column
`k` is skipped), and an insert state `I k` (emits residues between columns `k` and `k + 1`);
node `0` is the begin state, which acts as `M 0`, and the end state follows node `L`.

A path through the model that emits a sequence `x` is the same thing as an alignment of `x` to
the list of columns `[1, …, L]` (`columns L`): `(some a, some k)` is a visit to `M k` emitting
`a`, `(some a, none)` a visit to the insert state of the current node, `(none, some k)` a visit
to `D k`. The model is read as an `AlignmentAutomaton` whose control state is the previous state
type and the current node, so the sequence weight (forward) and the best path (Viterbi) are the
sum and the maximum over these alignments (`PairHMM.lean`).

The transition weights `trans k s t` go from the state of type `s` at node `k` to a state of
type `t` at the next node (`M`, `D`) or to the insert state `I k`. HMMER's Plan 7 architecture
(Eddy 1998) is the restriction `IsPlan7`: no `D → I` and no `I → D` transitions and no insert
states at nodes `0` and `L`. The original architecture of Krogh et al. allows them; the results
below hold for every transition weight function. HMMER's flanking states (`N`, `C`, `J`) and
local entry and exit transitions are not modeled: this is the core model, aligning the whole
sequence to the whole model.

## Main results

* `ProfileHMM.forward_eq_sum`: **the forward value is the total weight of all paths** (all
  alignments of the sequence to the model), the sequence's probability under the model when the
  weights are probabilities.
* `ProfileHMM.pathProb_le_viterbi`, `ProfileHMM.exists_pathProb_eq_viterbi`: **Viterbi is
  attained**; under nonnegative weights (`ProfileHMM.Nonneg`) it is the largest path weight:
  the best alignment of the sequence to the profile.
* `ProfileHMM.sum_pseudocountEmission`, `ProfileHMM.pseudocountEmission_pos`: match-state
  emission estimates from the residues of a multiple-alignment column with positive pseudocounts
  are a distribution with full support. Choosing the match columns of a multiple alignment and
  estimating transitions are not covered.

Both recursions peel the first residue or column (`AlignmentAutomaton.sumDP_cons_cons`,
`AlignmentAutomaton.maxDP_cons_cons`), so they run from the end of the model towards the
begin state: as for pair HMMs, this is the backward direction of Durbin et al., whose value at
the begin state is the forward score `P(x | model)`.

## Cost model

The recursions are specifications (exponential time if evaluated directly); tabulating them on
(residue position, node, state type) gives the usual `O(|x| L)` algorithms.

## References

* A. Krogh, M. Brown, I. S. Mian, K. Sjölander and D. Haussler, *Hidden Markov models in
  computational biology: applications to protein modeling*, J. Mol. Biol. 235 (1994),
  1501–1531.
* S. R. Eddy, *Profile hidden Markov models*, Bioinformatics 14 (1998), 755–763.
* R. Durbin, S. R. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, chapter 5.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.HMM

open Cslib.Algorithms.Lean

/-- The state types of a profile HMM node: match, insert, delete. -/
inductive ProfileState
  /-- Match: emit a residue aligned to the node's column. -/
  | M
  /-- Insert: emit a residue between two columns. -/
  | I
  /-- Delete: skip the node's column (silent). -/
  | D
  deriving DecidableEq, Repr

/-- A profile HMM with `L` consensus columns over the alphabet `α`, with weights in `R`.
`trans k s t` is the weight of a transition from the state of type `s` at node `k`
(`0 ≤ k ≤ L`; node `0` is the begin state, read as type `M`) to a state of type `t`: to `M`
or `D` at node `k + 1`, or to `I` at node `k`. `stop s` is the weight of the transition from the
state of type `s` at node `L` to the end state. -/
structure ProfileHMM (L : ℕ) (α R : Type*) where
  /-- The weight of a transition out of node `k` from type `s` to type `t`. -/
  trans : ℕ → ProfileState → ProfileState → R
  /-- The weight of the transition from node `L` to the end state. -/
  stop : ProfileState → R
  /-- The emission weight of a residue from the match state at node `k`. -/
  emitM : ℕ → α → R
  /-- The emission weight of a residue from the insert state at node `k`. -/
  emitI : ℕ → α → R

namespace ProfileHMM

/-- The consensus columns `[1, …, L]`. -/
def columns (L : ℕ) : List ℕ := List.range' 1 L

variable {L : ℕ} {α R : Type*}

/-- HMMER's Plan 7 restrictions (Eddy 1998): no delete-to-insert and no insert-to-delete
transitions, and no insert states at node `0` (the begin state) or node `L`. -/
structure IsPlan7 [Zero R] (h : ProfileHMM L α R) : Prop where
  /-- No `D → I` transitions. -/
  no_DI : ∀ k, h.trans k .D .I = 0
  /-- No `I → D` transitions. -/
  no_ID : ∀ k, h.trans k .I .D = 0
  /-- No insert state at the begin node. -/
  no_I₀ : ∀ s, h.trans 0 s .I = 0
  /-- No insert state at the last node. -/
  no_I_last : ∀ s, h.trans L s .I = 0

section Semiring

variable [Semiring R] (h : ProfileHMM L α R)

/-- The profile HMM as an alignment automaton reading alignments of a sequence to the columns
`[1, …, L]`. The control state is the type of the previous state and the current node (the last
column consumed); it starts at `(M, 0)`, the begin state. Reading `(some a, some j)` visits `M j`,
`(some a, none)` visits the insert state of the current node, `(none, some j)` visits `D j`; the
invalid column `(none, none)` has weight `0`. -/
def toAutomaton : AlignmentAutomaton (ProfileState × ℕ) α ℕ R where
  weight q c := match c with
    | (some a, some j) => h.trans q.2 q.1 .M * h.emitM j a
    | (some a, none) => h.trans q.2 q.1 .I * h.emitI q.2 a
    | (none, some _) => h.trans q.2 q.1 .D
    | (none, none) => 0
  next q c := match c with
    | (some _, some j) => (.M, j)
    | (some _, none) => (.I, q.2)
    | (none, some j) => (.D, j)
    | (none, none) => q
  final q := h.stop q.1

/-- The weight of a path through the model, given as an alignment `A` of the sequence to the
columns: the product of its transition and emission weights from the begin state to the end
state. -/
def pathProb (A : List (Option α × Option ℕ)) : R := h.toAutomaton.alignWeight (.M, 0) A

/-- The forward value of a sequence `x`: the total weight of all paths through the model that
emit `x` (`forward_eq_sum`), by the recursion on one residue and one column. -/
def forward (x : List α) : R := h.toAutomaton.sumDP (.M, 0) x (columns L)

/-- **Forward computes the total path weight**: the sum, over all alignments of `x` to the
columns `[1, …, L]` (all paths through the model emitting `x`, each once), of the path
weights. -/
theorem forward_eq_sum (x : List α) :
    h.forward x = ((alignmentsOf x (columns L)).map h.pathProb).sum :=
  h.toAutomaton.sumDP_eq_sum _ x _

end Semiring

section Viterbi

variable [Semiring R] [LinearOrder R] (h : ProfileHMM L α R)

/-- The Viterbi value of a sequence `x`: the value selected by the max recursion
(`pathProb_le_viterbi`, `exists_pathProb_eq_viterbi`). Under nonnegative weights it is the
largest weight of a path through the model emitting `x`. -/
def viterbi (x : List α) : R := h.toAutomaton.maxDP (.M, 0) x (columns L)

/-- Nonnegative transition and emission weights (the transitions to the end state may have any
sign: the Viterbi bound does not need them). -/
structure Nonneg : Prop where
  /-- Transitions are nonnegative. -/
  trans : ∀ k s t, 0 ≤ h.trans k s t
  /-- Match emissions are nonnegative. -/
  emitM : ∀ k a, 0 ≤ h.emitM k a
  /-- Insert emissions are nonnegative. -/
  emitI : ∀ k a, 0 ≤ h.emitI k a

variable {h}

/-- A profile HMM with nonnegative weights is a nonnegative alignment automaton. -/
theorem toAutomaton_nonneg [IsOrderedRing R] (hn : h.Nonneg) : h.toAutomaton.Nonneg := by
  rintro q ⟨_ | a, _ | j⟩
  · exact le_rfl
  · exact hn.trans _ _ _
  · exact mul_nonneg (hn.trans _ _ _) (hn.emitI _ _)
  · exact mul_nonneg (hn.trans _ _ _) (hn.emitM _ _)

/-- **Every path weighs at most the Viterbi value.** -/
theorem pathProb_le_viterbi [IsOrderedRing R] (hn : h.Nonneg) {x : List α}
    {A : List (Option α × Option ℕ)} (hA : A ∈ alignmentsOf x (columns L)) :
    h.pathProb A ≤ h.viterbi x :=
  AlignmentAutomaton.alignWeight_le_maxDP (toAutomaton_nonneg hn) _ hA

variable (h) in
/-- **The Viterbi value is attained**: some path (alignment of `x` to the profile) has
weight equal to the Viterbi value. Under nonnegative weights this attained value is the
largest path weight (`pathProb_le_viterbi`); without that hypothesis attainment alone
does not imply maximality. -/
theorem exists_pathProb_eq_viterbi (x : List α) :
    ∃ A ∈ alignmentsOf x (columns L), h.pathProb A = h.viterbi x :=
  h.toAutomaton.exists_alignWeight_eq_maxDP _ x _

end Viterbi

/-! ## Emission estimates from a multiple alignment -/

section Pseudocounts

variable {K : Type*} [Fintype α] [DecidableEq α] [Field K]

/-- The emission estimate of a match state from the residues `col` that a multiple alignment
places in its column (gaps omitted), with pseudocounts `pc` (Durbin et al., chapter 5;
Laplace's rule is `pc = 1`): `(count a + pc a) / (|col| + ∑ b, pc b)`. -/
def pseudocountEmission (col : List α) (pc : α → K) (a : α) : K :=
  ((col.count a : K) + pc a) / ((col.length : K) + ∑ b, pc b)

/-- With positive pseudocounts, the estimated emissions sum to one. -/
theorem sum_pseudocountEmission [LinearOrder K] [IsStrictOrderedRing K] [Nonempty α]
    (col : List α) {pc : α → K} (hpc : ∀ a, 0 < pc a) :
    ∑ a, pseudocountEmission col pc a = 1 := by
  have hpos : 0 < (col.length : K) + ∑ b, pc b :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _)
      (Finset.sum_pos (fun b _ => hpc b) Finset.univ_nonempty)
  simp only [pseudocountEmission]
  rw [← Finset.sum_div, Finset.sum_add_distrib, div_eq_one_iff_eq hpos.ne']
  congr 1
  have := Multiset.sum_count_eq_card (s := Finset.univ) (m := (col : Multiset α))
    (fun a _ => Finset.mem_univ a)
  simp only [Multiset.coe_count, Multiset.coe_card] at this
  exact_mod_cast this

/-- With positive pseudocounts, every residue gets a positive emission estimate, including
residues absent from the column. -/
theorem pseudocountEmission_pos [LinearOrder K] [IsStrictOrderedRing K] (col : List α)
    {pc : α → K} (hpc : ∀ a, 0 < pc a) (a : α) : 0 < pseudocountEmission col pc a :=
  div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (hpc a))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _)
      (Finset.sum_pos (fun b _ => hpc b) ⟨a, Finset.mem_univ a⟩))

end Pseudocounts

end ProfileHMM

end Cslib.Bioinformatics.HMM
