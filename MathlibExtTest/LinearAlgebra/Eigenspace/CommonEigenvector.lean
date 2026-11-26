/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v :=
  Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T hT

/-- Higher-universe consumer: field, space and index type in distinct universes. -/
example {K : Type 1} {V : Type 2} {ι : Type 3} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v :=
  Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T hT

/-- Boundary: the space must be nontrivial. On the zero space `PUnit` every
vector is `0`, so no family of endomorphisms has a common eigenvector. -/
example {K : Type*} [Field K] {ι : Type*} (T : ι → Module.End K PUnit) :
    ¬ ∃ v : PUnit, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  rintro ⟨v, hv, -⟩
  exact hv (Subsingleton.elim _ _)

/-- Boundary: the family must commute. On `K²` the nilpotent shifts `e₁ ↦ e₀` and
`e₀ ↦ e₁` (the matrices `!![0, 1; 0, 0]` and `!![0, 0; 1, 0]`) do not commute and have
no common eigenvector, over any field. -/
example {K : Type*} [Field K] : ¬ ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ i : Fin 2, ∃ c : K,
    (![!![0, 1; 0, 0], !![0, 0; 1, 0]] i : Matrix (Fin 2) (Fin 2) K).mulVecLin v = c • v := by
  rintro ⟨v, hv, hT⟩
  obtain ⟨c, hc⟩ := hT 0
  obtain ⟨d, hd⟩ := hT 1
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hd 0
  have h3 := congrFun hd 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2 h3
  apply hv
  funext i
  fin_cases i
  · rcases h2 with rfl | h2
    · simpa using h3
    · exact h2
  · rcases h1 with rfl | h1
    · simpa using h0
    · exact h1

/-- The theorem needs a nonzero space: it does not apply to the zero space `Fin 0 → K`,
which is finite-dimensional but not `Nontrivial`. -/
example {K : Type*} [Field K] [IsAlgClosed K] (T : Unit → Module.End K (Fin 0 → K)) : T = T := by
  fail_if_success
    have := Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T
      (fun i j h => (h (Subsingleton.elim i j)).elim)
  rfl
