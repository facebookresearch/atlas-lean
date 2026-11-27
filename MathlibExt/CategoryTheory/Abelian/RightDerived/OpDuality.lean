/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Injective.OpDuality
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.CommSq

/-!
# Right derivation and opposite left derivation

Right derivation is naturally isomorphic to the unop of left derivation
of the opposite functor. The comparison uses an injective resolution,
its opposite projective resolution and homology op-duality. Resolution
availability is specified on each side.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable [HasProjectiveResolutions Cᵒᵖ]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The right-derived object compared to the unop of the native
opposite left-derived object. -/
noncomputable def rightDerivedOpIsoApp (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) :
    (F.rightDerived n).obj X ≅ (F.op.leftDerived n).unop.obj X :=
  let J := injectiveResolution X
  let P := injectiveResolutionOpProj J
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  J.isoRightDerivedObj F n ≪≫ (K.homologyOp n).unop ≪≫
    (P.isoLeftDerivedObj F.op n).unop

/-- The object-op comparison commutes with the derived maps. -/
lemma rightDerivedOpIsoApp_naturality (F : C ⥤ D) [F.Additive] (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (F.rightDerived n).map f ≫ (F.rightDerivedOpIsoApp n Y).hom =
      (F.rightDerivedOpIsoApp n X).hom ≫ (F.op.leftDerived n).unop.map f := by
  let JX := injectiveResolution X
  let JY := injectiveResolution Y
  let PX := injectiveResolutionOpProj JX
  let PY := injectiveResolutionOpProj JY
  let d : JX.cocomplex ⟶ JY.cocomplex := InjectiveResolution.desc f JY JX
  have hd₀ : JX.ι.f 0 ≫ d.f 0 = f ≫ JY.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f JY JX
  let φ : PY.complex ⟶ PX.complex :=
    (HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map d.op
  have hcomm : φ.f 0 ≫ PX.π.f 0 = PY.π.f 0 ≫ f.op := by
    change (d.f 0).op ≫ ((JX.ι.f 0).op ≫ 𝟙 (Opposite.op X)) =
      ((JY.ι.f 0).op ≫ 𝟙 (Opposite.op Y)) ≫ f.op
    simp only [CochainComplex.single₀_obj_zero, Category.comp_id]
    change (JX.ι.f 0 ≫ d.f 0).op = (f ≫ JY.ι.f 0).op
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
  let Mmap := (F.op.leftDerived n).unop.map f
  have hA := InjectiveResolution.isoRightDerivedObj_hom_naturality
    f JX JY d hd₀ F n
  have hB := congrArg Quiver.Hom.unop
    (HomologicalComplex.homologyOp_hom_naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map d) n)
  have hC := congrArg Quiver.Hom.unop
    (ProjectiveResolution.isoLeftDerivedObj_hom_naturality
      f.op PY PX φ hcomm F.op n)
  simp only [unop_comp] at hC
  have sA : CommSq aX ((F.rightDerived n).map f) Hmap aY := ⟨hA.symm⟩
  have sB : CommSq bX Hmap Nmap bY := ⟨hB⟩
  have sC : CommSq cX Nmap Mmap cY := ⟨hC⟩
  change (F.rightDerived n).map f ≫ (aY ≫ bY ≫ cY) =
    (aX ≫ bX ≫ cX) ≫ Mmap
  exact (sA.horiz_comp (sB.horiz_comp sC)).w.symm

/-- The natural comparison between right derivation and opposite
left derivation. -/
noncomputable def rightDerivedOpIso (F : C ⥤ D) [F.Additive] (n : ℕ) :
    F.rightDerived n ≅ (F.op.leftDerived n).unop :=
  NatIso.ofComponents (F.rightDerivedOpIsoApp n)
    (fun f => F.rightDerivedOpIsoApp_naturality n f)

end CategoryTheory.Functor
