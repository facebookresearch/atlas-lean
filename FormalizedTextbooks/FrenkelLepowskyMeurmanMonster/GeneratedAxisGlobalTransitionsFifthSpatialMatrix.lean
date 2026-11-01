/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixWord

/-! Exact rational spatial matrices for the actual fifth-axis normalization words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The rational matrix of the original inverse-coordinate permutation convention. -/
def generatedAxisGlobalSpatialPermutationMatrix (p : Equiv.Perm (Fin 24)) :
    Matrix (Fin 24) (Fin 24) ℚ := fun i j => if p.symm i = j then 1 else 0

/-- The rational diagonal of the actual Golay coordinate signs. -/
def generatedAxisGlobalSpatialSignMatrix (d : golayCode) :
    Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.diagonal (fun i => if d.val i = 0 then 1 else -1)

/-- Rational matrices act by the exact source permutation on every real vector. -/
theorem generatedAxisGlobalSpatialPermutationMatrix_actual (p : golayAutomorphismSubgroup)
    (x : Fin 24 → ℝ) :
    (generatedAxisGlobalSpatialPermutationMatrix p.val).map (Rat.castHom ℝ) *ᵥ x =
      (golayPermutationIsometry p).val x := by
  funext i
  simp [generatedAxisGlobalSpatialPermutationMatrix, Matrix.mulVec, dotProduct,
    golayPermutationIsometry, golayRealPermute, apply_ite]

/-- Rational diagonal signs act by the genuine Golay lattice isometry. -/
theorem generatedAxisGlobalSpatialSignMatrix_actual (d : golayCode) (x : Fin 24 → ℝ) :
    (generatedAxisGlobalSpatialSignMatrix d).map (Rat.castHom ℝ) *ᵥ x =
      (golaySignIsometry d).val x := by
  funext i
  by_cases hi : d.val i = 0 <;>
    simp [generatedAxisGlobalSpatialSignMatrix, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply, golaySignIsometry, golayRealSign, qSign, apply_ite, hi]

/-- One complete original spatial stage, retaining its actual order and optional Xi orientation. -/
def generatedAxisGlobalFifthSpatialStageMatrix (k : Fin 14) (j : Fin 7) :
    Matrix (Fin 24) (Fin 24) ℚ :=
  (if generatedAxisGlobalFifthShortNormalizationXi k j then co1XiMatrixQ else 1) *
    (generatedAxisGlobalSpatialSignMatrix
      (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns k j)) *
      generatedAxisGlobalSpatialPermutationMatrix
        (generatedAxisGlobalFifthShortNormalizationPermutation k j).val)

/-- Every rational stage is the entire actual physical spatial operator. -/
theorem generatedAxisGlobalFifthSpatialStageMatrix_actual (k : Fin 14) (j : Fin 7)
    (x : Fin 24 → ℝ) :
    (generatedAxisGlobalFifthSpatialStageMatrix k j).map (Rat.castHom ℝ) *ᵥ x =
      (generatedAxisGlobalFifthShortNormalizationSpatial k j).val x := by
  rw [generatedAxisGlobalFifthSpatialStageMatrix, Matrix.map_mul, Matrix.map_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    generatedAxisGlobalSpatialPermutationMatrix_actual,
    generatedAxisGlobalSpatialSignMatrix_actual]
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j with
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte,
      generatedAxisGlobalFifthShortNormalizationSpatial, one_mul]
    have h1 : (1 : Matrix (Fin 24) (Fin 24) ℚ).map (Rat.castHom ℝ) = 1 := by
      ext i j
      simp [Matrix.map_apply, Matrix.one_apply, apply_ite]
    rw [h1, Matrix.one_mulVec]
    rfl
  | true =>
    simp only [hx, ↓reduceIte, generatedAxisGlobalFifthShortNormalizationSpatial]
    rfl

/-- The complete rational matrix of the identical chronological seven-stage spatial word. -/
def generatedAxisGlobalFifthSpatialWordMatrix (k : Fin 14) :
    Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthSpatialStageMatrix k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- Each full rational matrix acts exactly as the original actual Co0 word on every real vector. -/
theorem generatedAxisGlobalFifthSpatialWordMatrix_actual (k : Fin 14) (x : Fin 24 → ℝ) :
    (generatedAxisGlobalFifthSpatialWordMatrix k).map (Rat.castHom ℝ) *ᵥ x =
      (generatedAxisGlobalFifthShortSpatialWord k).val x := by
  have hc : ∀ n, ∀ x : Fin 24 → ℝ,
      (generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthSpatialStageMatrix k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n).map (Rat.castHom ℝ) *ᵥ x =
      (generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationSpatial k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n).val x := by
    intro n
    induction n with
    | zero => intro x; simp [generatedAxisGlobalWordChain]
    | succ n ih =>
      intro x
      rw [generatedAxisGlobalWordChain, Matrix.map_mul, ← Matrix.mulVec_mulVec, ih,
        generatedAxisGlobalFifthSpatialStageMatrix_actual, generatedAxisGlobalWordChain]
      rfl
  exact hc 7 x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
