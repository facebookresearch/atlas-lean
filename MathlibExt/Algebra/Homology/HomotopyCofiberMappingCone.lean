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
# The native arrow-category cofiber map is the native cochain mapping-cone map

Both existing constructions have the same shifted-source and target
inclusion components. Their native extensionality proves the equality.
This exposes the map identification needed to reuse the native mapping-cone
triangle morphism for arbitrary coefficient families. Only preadditivity
and binary biproducts are needed; no abelian, exactness or flatness premise
is imposed here, and no new cone construction is introduced.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The two native strict-square maps of the same native cochain cone coincide. -/
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
