/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.OpDuality

/-!
# Computing right-derived opposite duality on a supplied resolution

Let `C,D` be abelian, with injective resolutions in `C` and projective
resolutions in `Cᵒᵖ`, and let `F : C → D` be additive. The natural
opposite-derived comparison can be computed from any injective
resolution of `X`, using its opposite projective resolution, homology
opposite duality, and the two canonical derived-resolution comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable [HasProjectiveResolutions Cᵒᵖ]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C` and
projective resolutions in `Cᵒᵖ`, and `F : C → D` additive.
For any injective resolution `J` of `X`, the degree-`n` opposite-derived
comparison is the canonical comparison to `Hⁿ(F(J))`, followed by
homology opposite duality and the unop of the left-derived comparison
for the opposite projective resolution of `J`. -/
theorem rightDerivedOpIsoApp_hom_ofInjectiveResolution {X : C} (J : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    ((F.rightDerivedOpIso n).app X).hom =
      (J.isoRightDerivedObj F n).hom ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homologyOp n).hom).unop ≫
      ((injectiveResolutionOpProj J).isoLeftDerivedObj F.op n).hom.unop := by
  let JX := J
  let JY := injectiveResolution X
  let PX := injectiveResolutionOpProj JX
  let PY := injectiveResolutionOpProj JY
  let d : JX.cocomplex ⟶ JY.cocomplex := InjectiveResolution.desc (𝟙 X) JY JX
  have hd₀ : JX.ι.f 0 ≫ d.f 0 = (𝟙 X) ≫ JY.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero (𝟙 X) JY JX
  let φ : PY.complex ⟶ PX.complex :=
    (HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map d.op
  have hcomm : φ.f 0 ≫ PX.π.f 0 = PY.π.f 0 ≫ (𝟙 X).op := by
    change (d.f 0).op ≫ ((JX.ι.f 0).op ≫ 𝟙 (Opposite.op X)) =
      ((JY.ι.f 0).op ≫ 𝟙 (Opposite.op X)) ≫ (𝟙 X).op
    simp only [CochainComplex.single₀_obj_zero, Category.comp_id]
    change (JX.ι.f 0 ≫ d.f 0).op = ((𝟙 X) ≫ JY.ι.f 0).op
    exact congrArg Quiver.Hom.op hd₀
  let aX := (JX.isoRightDerivedObj F n).hom
  let aY := (JY.isoRightDerivedObj F n).hom
  let bX := (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    JX.cocomplex).homologyOp n).hom.unop
  let bY := (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    JY.cocomplex).homologyOp n).hom.unop
  let cX := (PX.isoLeftDerivedObj F.op n).hom.unop
  let cY := (PY.isoLeftDerivedObj F.op n).hom.unop
  let Hmap := (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map d
  let Nmap := ((F.op.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n).map φ).unop
  let Mmap := (F.op.leftDerived n).unop.map (𝟙 X)
  have hA := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 X) JX JY d hd₀ F n
  have hB := congrArg Quiver.Hom.unop
    (HomologicalComplex.homologyOp_hom_naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map d) n)
  have hC := congrArg Quiver.Hom.unop
    (ProjectiveResolution.isoLeftDerivedObj_hom_naturality
      (𝟙 X).op PY PX φ hcomm F.op n)
  simp only [unop_comp] at hC
  have sA : CommSq aX ((F.rightDerived n).map (𝟙 X)) Hmap aY := ⟨hA.symm⟩
  have sB : CommSq bX Hmap Nmap bY := ⟨hB⟩
  have sC : CommSq cX Nmap Mmap cY := ⟨hC⟩
  change (aY ≫ bY ≫ cY) = (aX ≫ bX ≫ cX)
  have h := (sA.horiz_comp (sB.horiz_comp sC)).w.symm
  dsimp only [Mmap] at h
  simp only [Functor.map_id] at h
  exact (Category.id_comp (aY ≫ bY ≫ cY)).symm.trans
    (h.trans (Category.comp_id (aX ≫ bX ≫ cX)))

end CategoryTheory.Functor
