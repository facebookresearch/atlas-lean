/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Maximum `n`-times coverage

Liu, Dimitrakakis, Carter and Gifford introduce *maximum `n`-times coverage* for peptide vaccine
design. Elements `i : X` (e.g. HLA haplotypes) carry weights `w i ≥ 0`; each overlay `j : A`
(e.g. a peptide) covers element `i` some number of times `c j i : ℕ`. A set `O` of overlays
covers `i` `coverCount c O i = ∑ j ∈ O, c j i` times, and the `n`-times coverage function is
`nCoverage w c n O = ∑ i, w i · 𝟙[coverCount c O i ≥ n]`
(equations (1)–(2) of the paper). The problem is to maximize it over `|O| ≤ k`.

## Main results

* `nCoverage_mono`: for nonnegative weights the objective is monotone.
* `not_isSubmodular_nCoverage`: **Theorem 1** of the paper: for every `n ≥ 2` there is an
  instance (here: `n` overlays each covering a single element once) on which `nCoverage` is not
  submodular, so the greedy `(1 - 1/e)` guarantee for submodular maximization does not apply.
  The paper's appendix gives an `n = 2` example and says that similar ones exist for every
  `n > 1`.
* `isSubmodular_nCoverage_one`: in contrast, for `n = 1` (ordinary weighted maximum coverage)
  the objective is submodular for nonnegative weights.

NP-completeness of the decision version is stated in
`WantedExt/Complexity/NPComplete/MaxNTimesCoverageWanted.lean`.

## References

* G. Liu, A. Dimitrakakis, B. Carter and D. Gifford, "Maximum n-times coverage for vaccine
  design", *International Conference on Learning Representations (ICLR)*, 2022.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MaxNTimesCoverage

open Finset

variable {A X : Type*}

/-- The number of times the overlays `O` cover the element `i` (equation (1)). -/
def coverCount (c : A → X → ℕ) (O : Finset A) (i : X) : ℕ := ∑ j ∈ O, c j i

/-- The `n`-times coverage function: the total weight of the elements covered at least `n`
times by `O` (equation (2)). -/
def nCoverage [Fintype X] (w : X → ℝ) (c : A → X → ℕ) (n : ℕ) (O : Finset A) : ℝ :=
  ∑ i, if n ≤ coverCount c O i then w i else 0

/-- A set function is submodular if adding an element to a larger set gains at most as much
as adding it to a smaller set (the diminishing-returns form, Definition 2 of the paper). -/
def IsSubmodular [DecidableEq A] (f : Finset A → ℝ) : Prop :=
  ∀ S T : Finset A, ∀ x, S ⊆ T → x ∉ T → f (insert x T) - f T ≤ f (insert x S) - f S

/-- More overlays cover every element at least as often. -/
theorem coverCount_mono (c : A → X → ℕ) {O O' : Finset A} (h : O ⊆ O') (i : X) :
    coverCount c O i ≤ coverCount c O' i :=
  sum_le_sum_of_subset h

/-- For nonnegative weights the `n`-times coverage function is monotone. -/
theorem nCoverage_mono [Fintype X] {w : X → ℝ} (hw : ∀ i, 0 ≤ w i) (c : A → X → ℕ) (n : ℕ)
    {O O' : Finset A} (h : O ⊆ O') : nCoverage w c n O ≤ nCoverage w c n O' := by
  refine sum_le_sum fun i _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans (coverCount_mono c h i)) h2
  · exact hw i
  · exact le_rfl

/-- **The `n`-times coverage function is not submodular** (Liu et al., Theorem 1): for every
`n ≥ 2`, take `n` overlays that each cover a single element of weight `1` once. Adding the last
overlay to the other `n - 1` gains `1`; adding it to `∅` gains `0`. -/
theorem not_isSubmodular_nCoverage {n : ℕ} (hn : 2 ≤ n) :
    ¬IsSubmodular (nCoverage (fun _ : Unit => (1 : ℝ)) (fun (_ : Fin n) _ => 1) n) := by
  intro hsub
  have h0 : (⟨0, by omega⟩ : Fin n) ∉ univ.erase ⟨0, by omega⟩ := notMem_erase _ _
  have key := hsub ∅ (univ.erase ⟨0, by omega⟩) ⟨0, by omega⟩ (empty_subset _) h0
  simp only [nCoverage, coverCount, sum_const, smul_eq_mul, mul_one, Fintype.univ_unit,
    insert_erase (mem_univ _), card_univ, Fintype.card_fin, insert_empty,
    card_singleton, card_empty, card_erase_of_mem (mem_univ _)] at key
  simp [show ¬n ≤ n - 1 by omega, show ¬n ≤ 1 by omega, show ¬n ≤ 0 by omega] at key
  linarith

/-- For `n = 1` (weighted maximum coverage) and nonnegative weights, the objective is
submodular. -/
theorem isSubmodular_nCoverage_one [Fintype X] [DecidableEq A] {w : X → ℝ}
    (hw : ∀ i, 0 ≤ w i) (c : A → X → ℕ) : IsSubmodular (nCoverage w c 1) := by
  intro S T x hST hxT
  have hxS : x ∉ S := fun h => hxT (hST h)
  simp only [nCoverage, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  have hS : coverCount c (insert x S) i = c x i + coverCount c S i := sum_insert hxS
  have hT : coverCount c (insert x T) i = c x i + coverCount c T i := sum_insert hxT
  have hmono := coverCount_mono c hST i
  rw [hS, hT]
  split_ifs <;> linarith [hw i]

end Cslib.Algorithms.Lean.MaxNTimesCoverage
