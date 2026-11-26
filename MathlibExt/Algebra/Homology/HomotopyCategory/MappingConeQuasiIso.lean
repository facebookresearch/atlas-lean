/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import MathlibExt.Algebra.Homology.HomotopyCofiberQuasiIso

/- The quasi-isomorphism proof uses the cone triangles and the triangle five lemma in the derived category. -/

/-!
# Cone maps from homotopy-commuting squares

For integer cochain maps `φ₁ : K₁ → L₁`, `φ₂ : K₂ → L₂`, maps
`a : K₁ → K₂`, `b : L₁ → L₂`, and a homotopy from `φ₁ ≫ b`
to `a ≫ φ₂`, there is a map `Cone(φ₁) → Cone(φ₂)`.
In biproduct coordinates it uses `a` on the shifted first factor,
`b` on the second factor, and the stated homotopy as the cross
component. In an abelian category, quasi-isomorphisms of both vertex
maps make this cone map a quasi-isomorphism.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

section Components

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
variable {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}

/-- Let `C` be preadditive with binary biproducts, and let
`φ₁ : K₁ → L₁`, `φ₂ : K₂ → L₂` be integer cochain maps.
For `a : K₁ → K₂`, `b : L₁ → L₂` and a homotopy
`H : φ₁ ≫ b ≃ a ≫ φ₂`, the cone map in degree `j` has first
component `a_(j+1)`, second component `b_j`, cross component
`+H_(j+1,j)` from the shifted first source to the second target,
and zero in the other off-diagonal position. -/
theorem mapOfHomotopy_f (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (j : ℤ) :
    (mapOfHomotopy H).f j =
      (fst φ₁).1.v j (j + 1) rfl ≫
          (a.f (j + 1) ≫ (inl φ₂).v (j + 1) j (by omega) +
            H.hom (j + 1) j ≫ (inr φ₂).f j) +
        (snd φ₁).v j j (add_zero j) ≫ b.f j ≫ (inr φ₂).f j := by
  have hH : ((HomComplex.Cochain.equivHomotopy (φ₁ ≫ b) (a ≫ φ₂)) H).1.v
      (j + 1) j (by omega) = H.hom (j + 1) j := rfl
  simp only [mapOfHomotopy, desc_f _ _ _ _ j (j + 1) rfl,
    HomComplex.Cochain.add_v, HomComplex.Cochain.zero_cochain_comp_v,
    HomComplex.Cochain.comp_zero_cochain_v, HomComplex.Cochain.ofHom_v,
    hH, HomologicalComplex.comp_f]

end Components

section QuasiIso

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
variable {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}

/-- In an abelian category `C`, let `φ₁,φ₂` be integer cochain
maps and `a,b` their two vertex maps, with homotopy
`φ₁ ≫ b ≃ a ≫ φ₂`. If `a,b` are quasi-isomorphisms, the induced
map `Cone(φ₁) → Cone(φ₂)` is a quasi-isomorphism. -/
theorem quasiIso_mapOfHomotopy (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))
    (ha : QuasiIso a) (hb : QuasiIso b) : QuasiIso (mapOfHomotopy H) := by
  let _ := HasDerivedCategory.standard C
  let t : (DerivedCategory.Qh (C := C)).mapTriangle.obj (triangleh φ₁) ⟶
      (DerivedCategory.Qh (C := C)).mapTriangle.obj (triangleh φ₂) :=
    (DerivedCategory.Qh (C := C)).mapTriangle.map (trianglehMapOfHomotopy H)
  have h₁ : IsIso t.hom₁ :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) a).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C a).2 ha)
  have h₂ : IsIso t.hom₂ :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) b).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C b).2 hb)
  have h₃ : IsIso t.hom₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ t
    ((DerivedCategory.Qh (C := C)).map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₁))
    ((DerivedCategory.Qh (C := C)).map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₂)) h₁ h₂
  have hQ : IsIso (DerivedCategory.Q.map (mapOfHomotopy H)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) (mapOfHomotopy H)).1 h₃
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso C (mapOfHomotopy H)).1 hQ

end QuasiIso

end CochainComplex.mappingCone

end
