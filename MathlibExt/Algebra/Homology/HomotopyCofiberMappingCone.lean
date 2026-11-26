/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping-cone map of a strict arrow square

For integer cochain complexes in a preadditive category with binary biproducts, a strictly
commuting square of arrows induces a map on their cofibers. This arrow-category map equals the
mapping-cone map defined by the square's source and target maps, with the same shifted-source
and target summand components.

The equality retains the stated predecessor witness for the integer cochain shape.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The arrow cofiber map equals the strict-square mapping-cone map.

For an arrow morphism between φ and ψ and the stated predecessor witness, mapArrowHom agrees
with mappingCone.map on its source and target maps. -/
theorem mapArrowHom_eq_mappingCone_map
    {F G F' G' : CochainComplex C ℤ} {φ : F ⟶ G} {ψ : F' ⟶ G'}
    (hc : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j)
    (a : Arrow.mk φ ⟶ Arrow.mk ψ) :
    mapArrowHom φ ψ hc a = CochainComplex.mappingCone.map φ ψ a.left a.right a.w.symm := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.mappingCone.ext_from φ (n + 1) n rfl
  · change inlX φ (n + 1) n rfl ≫ (mapArrowHom φ ψ hc a).f n =
      (CochainComplex.mappingCone.inl φ).v (n + 1) n (by simp) ≫
        (CochainComplex.mappingCone.map φ ψ a.left a.right a.w.symm).f n
    rw [inlX_mapArrowHom hc a (n + 1) n rfl]
    rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_v_desc_f]
    simp [CochainComplex.mappingCone.inl]
    rfl
  · change inrX φ n ≫ (mapArrowHom φ ψ hc a).f n =
      (CochainComplex.mappingCone.inr φ).f n ≫
        (CochainComplex.mappingCone.map φ ψ a.left a.right a.w.symm).f n
    rw [inrX_mapArrowHom hc a n]
    rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_f_desc_f]
    rfl

end HomologicalComplex.homotopyCofiber

end
