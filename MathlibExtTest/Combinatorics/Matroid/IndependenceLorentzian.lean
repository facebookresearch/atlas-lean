/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.IndependenceLorentzian
import Mathlib.Combinatorics.Matroid.Map

open Finsupp MvPolynomial
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials
open MathlibExt.Combinatorics.Matroid.MConvex

namespace MathlibExt.Combinatorics.LorentzianToolboxWanted.IndependenceLorentzianTest

private lemma indicatorVec_empty {α : Type*} : indicatorVec (∅ : Finset α) = 0 := by
  classical ext; simp [indicatorVec_apply]

-- When all elements are loops, the empty set contributes the only term, even for n = 0.
example (n : ℕ) :
    (⟨X 0 ^ n, isHomogeneous_X_pow 0 n⟩ : H (n + 1) n) ∈ L (n + 1) n := by
  classical
  apply independenceGeneratingPolynomial_mem_L (Matroid.loopyOn Set.univ)
  have hs : Finset.univ.filter (fun A : Finset (Fin n) =>
      (Matroid.loopyOn Set.univ).Indep (A : Set (Fin n))) = {∅} := by
    ext A
    simp
  rw [hs]
  simp [indicatorVec_empty, X_pow_eq_monomial]

-- Two parallel nonloops contribute both singletons and exclude their pair.
private noncomputable def parallelPairForm : H 3 2 :=
  ⟨X 0 ^ 2 + X 0 * X 1 + X 0 * X 2,
    ((isHomogeneous_X_pow 0 2).add ((isHomogeneous_X ℝ 0).mul (isHomogeneous_X ℝ 1))).add
      ((isHomogeneous_X ℝ 0).mul (isHomogeneous_X ℝ 2))⟩

example : parallelPairForm ∈ L 3 2 := by
  classical
  let M := (Matroid.freeOn (Set.univ : Set Unit)).comap (fun _ : Fin 2 => ())
  apply independenceGeneratingPolynomial_mem_L M
  have sets : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have indicator (i : Fin 3) : indicatorVec {i} = single i 1 := by
    ext j
    simp [indicatorVec_apply, single_apply, eq_comm]
  have hs : Finset.univ.filter (fun A : Finset (Fin 2) => M.Indep (A : Set (Fin 2))) =
      {∅, {0}, {1}} := by
    ext A
    rw [sets]
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, hI⟩
      rcases h with rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · have := (Matroid.comap_indep_iff.mp hI).2
        simp at this
    · intro h
      rcases h with rfl | rfl | rfl <;> simp [M]
  rw [hs]
  simp only [parallelPairForm, X_pow_eq_monomial]
  norm_num [← Finsupp.single_tsub, indicator, indicatorVec_empty, X, monomial_mul_monomial,
    Finset.sum_insert, Finset.sum_singleton, add_comm, add_left_comm]
  exact add_comm _ _

end MathlibExt.Combinatorics.LorentzianToolboxWanted.IndependenceLorentzianTest
