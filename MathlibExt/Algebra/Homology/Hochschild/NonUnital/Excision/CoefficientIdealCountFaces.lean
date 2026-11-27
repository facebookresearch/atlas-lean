/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.IdealCountFaces

/-!
# Passive coefficients under ideal-count multiplication faces

For a non-wrapping regular face of an algebra word, tensoring with identity on a ground module
V leaves the coefficient unchanged. If the input span requires r entries in a two-sided ideal,
the image requires at least r−1 ideal entries. The statement holds for arbitrary V.
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let V be any k-module. For n,r : ℕ and i : Fin (n + 1), the
image of coefficientIdealWordSpan V (n + 2) r under id_V ⊗ regularWordFace n i.castSucc lies
in coefficientIdealWordSpan V (n + 1) (r−1). Only adjacent non-wrapping faces occur. -/
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
