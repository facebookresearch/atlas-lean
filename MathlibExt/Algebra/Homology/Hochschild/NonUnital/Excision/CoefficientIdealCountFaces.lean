/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.IdealCountFaces

/-!
# Coefficient words under ideal-count bar faces

Non-wrapping regular faces act on algebra tensor
words and leave arbitrary coefficients fixed.
Their word-coordinate formulas determine the
corresponding span maps for the truncated boundary.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (V : Type w) [AddCommGroup V] [Module k V]

/-- The identity-coefficient adjacent face loses at most one required ideal word entry. -/
theorem coefficientIdealWordSpan_regularWordFace (n required : ℕ) (i : Fin (n + 1)) :
    (coefficientIdealWordSpan k A I V (n + 2) required).map
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (regularWordFace k A n i.castSucc)) ≤
      coefficientIdealWordSpan k A I V (n + 1) (required - 1) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, a, ha, rfl⟩
  change TensorProduct.map (LinearMap.id : V →ₗ[k] V)
      (regularWordFace k A n i.castSucc) (v ⊗ₜ[k] PiTensorProduct.tprod k a) ∈
    coefficientIdealWordSpan k A I V (n + 1) (required - 1)
  rw [TensorProduct.map_tmul, LinearMap.id_apply, regularWordFace_castSucc_tprod]
  apply Submodule.subset_span
  refine ⟨v, hochschildMulAdjacent i a, ?_, rfl⟩
  have hcount := idealEntryCount_mulAdjacent k A I i a
  omega

end ModuleCat.Algebra.Hochschild.NonUnital
