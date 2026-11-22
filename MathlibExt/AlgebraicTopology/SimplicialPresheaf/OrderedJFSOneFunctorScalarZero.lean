/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorObject

/-!
# The original functor object's zero row and scalar mapping end

The original constant presheaf and Cartesian evaluation use the same scalar
tensor as the original end adjunction. Right-adjoint uniqueness compares the
entire zero row with that end, with its actual transpose for every scalar.
-/

noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialPresheaf.OrderedJFS.OneFunctor

open SimplicialSpace.WholePowerZeroOriginalMappingIso

/-- Evaluate the original zero row after the specified one-fold designation. -/
@[implicit_reducible] def zero : Original.{u} 1 ⥤ SSet.{u} :=
  oneDesignatedEquivalence.functor ⋙ outerZero

/-- The literal constant original presheaf, retaining every inner scalar. -/
@[implicit_reducible] def scalarConst : SSet.{u} ⥤ Original.{u} 1 :=
  Functor.const (FinitePowerSite.Source 1)ᵒᵖ

private def scalarConstIso : outerConst ⋙ oneDesignatedEquivalence.{u}.inverse ≅ scalarConst :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L k
    ext a
    rfl)

/-- The existing zero-row adjunction transported to the literal original constant presheaf. -/
def scalarConstAdjunction : scalarConst.{u} ⊣ zero.{u} :=
  (outerConstAdjunction.comp oneDesignatedEquivalence.symm.toAdjunction).ofNatIsoLeft
    scalarConstIso

/-- Cartesian tensor with the literal constant scalar is the original scalar tensor. -/
def tensorScalarIso (A : Original.{u} 1) :
    scalarConst ⋙ tensorLeft A ≅ scalarTensor.obj A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L k
    ext a
    rfl)

/-- The same original Cartesian adjunction represents the full zero row. -/
def zeroAdjunction (A : Original.{u} 1) :
    scalarTensor.obj A ⊣ objectFunctor A ⋙ zero :=
  (scalarConstAdjunction.comp (adjunction A)).ofNatIsoLeft (tensorScalarIso A)

/-- The native Cartesian transpose after the literal scalar-tensor comparison. -/
def scalarCurry (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (f : (scalarTensor.obj A).obj K ⟶ Z) : scalarConst.obj K ⟶ object A Z :=
  curry ((tensorScalarIso A).hom.app K ≫ f)

/-- The actual constant-scalar unit followed by the native Cartesian transpose at zero. -/
def zeroTranspose (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (f : (scalarTensor.obj A).obj K ⟶ Z) : K ⟶ zero.obj (object A Z) :=
  scalarConstAdjunction.unit.app K ≫ zero.map (scalarCurry A K Z f)

/-- The scalar adjunct uses these same native maps and the literal tensor comparison. -/
theorem zeroAdjunction_homEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (f : (scalarTensor.obj A).obj K ⟶ Z) :
    (zeroAdjunction A).homEquiv K Z f = zeroTranspose A K Z f := by
  unfold zeroAdjunction
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  change scalarConstAdjunction.homEquiv K (object A Z) (scalarCurry A K Z f) = _
  exact Adjunction.homEquiv_unit scalarConstAdjunction K (object A Z) _

/-- At every inner degree the constant-scalar unit keeps the original scalar point. -/
theorem scalarConstAdjunction_unit_app (K : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : K.obj n) : (scalarConstAdjunction.unit.app K).app n x = x := by
  rfl

/-- Every inner point of the zero transpose is the original Cartesian transpose's zero-row point. -/
theorem zeroTranspose_app (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (f : (scalarTensor.obj A).obj K ⟶ Z) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    (zeroTranspose A K Z f).app n x =
      ((oneDesignatedEquivalence.functor.map (scalarCurry A K Z f)).hom.app (op ⦋0⦌)).app n x := by
  change (zero.map (scalarCurry A K Z f)).app n
    ((scalarConstAdjunction.unit.app K).app n x) = _
  rw [scalarConstAdjunction_unit_app]
  rfl

/-- Scalar maps are retained by the original zero transpose. -/
theorem zeroTranspose_scalar (A : Original.{u} 1) {K L : SSet.{u}}
    (k : K ⟶ L) (Z : Original.{u} 1) (f : (scalarTensor.obj A).obj L ⟶ Z) :
    zeroTranspose A K Z ((scalarTensor.obj A).map k ≫ f) = k ≫ zeroTranspose A L Z f := by
  rw [← zeroAdjunction_homEquiv, ← zeroAdjunction_homEquiv]
  exact (zeroAdjunction A).homEquiv_naturality_left k f

/-- Source precomposition retains the original constant-scalar Cartesian transpose. -/
theorem scalarCurry_source {A B : Original.{u} 1} (f : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (g : (scalarTensor.obj B).obj K ⟶ Z) :
    scalarCurry A K Z ((scalarTensor.map f).app K ≫ g) =
      scalarCurry B K Z g ≫ sourceMap f Z := by
  unfold scalarCurry
  rw [← curry_source]
  congr 1

/-- The entire zero-row transpose has the same original source action. -/
theorem zeroTranspose_source {A B : Original.{u} 1} (f : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (g : (scalarTensor.obj B).obj K ⟶ Z) :
    zeroTranspose A K Z ((scalarTensor.map f).app K ≫ g) =
      zeroTranspose B K Z g ≫ zero.map (sourceMap f Z) := by
  unfold zeroTranspose
  rw [scalarCurry_source, zero.map_comp, Category.assoc]

/-- The entire original zero row is the original scalar mapping end. -/
def zeroScalarNatIso (A : Original.{u} 1) :
    objectFunctor A ⋙ zero ≅ innerHomFunctor.obj (op A) :=
  (zeroAdjunction A).rightAdjointUniq (scalarTensorHomAdjunction A)

/-- Its component retains the specified source and target before any scalar evaluation. -/
def zeroScalarIso (A Z : Original.{u} 1) : zero.obj (object A Z) ≅ innerHom A Z :=
  (zeroScalarNatIso A).app Z

/-- Every original scalar sees the same Cartesian and scalar-end transpose. -/
theorem zeroScalarIso_characteristic (A : Original.{u} 1) (K : SSet.{u})
    (Z : Original.{u} 1) (f : (scalarTensor.obj A).obj K ⟶ Z) :
    zeroTranspose A K Z f ≫ (zeroScalarIso A Z).hom = scalarTensorHomEquiv A K Z f := by
  rw [← zeroAdjunction_homEquiv]
  change (zeroAdjunction A).homEquiv K Z f ≫
    ((zeroAdjunction A).rightAdjointUniq (scalarTensorHomAdjunction A)).hom.app Z = _
  have h : (zeroAdjunction A).homEquiv K Z f ≫
      ((zeroAdjunction A).rightAdjointUniq (scalarTensorHomAdjunction A)).hom.app Z =
      (scalarTensorHomAdjunction A).homEquiv K Z f := by
    rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Category.assoc,
      (((zeroAdjunction A).rightAdjointUniq (scalarTensorHomAdjunction A)).hom.naturality f),
      ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  exact h.trans (congrArg (fun e => e K Z f) (scalarTensorHomAdjunction_homEquiv A))

/-- The inverse comparison uses the same original scalar-end and Cartesian adjuncts. -/
theorem zeroScalarIso_inverse_characteristic (A : Original.{u} 1) (K : SSet.{u})
    (Z : Original.{u} 1) (h : K ⟶ innerHom A Z) :
    ((zeroAdjunction A).homEquiv K Z).symm (h ≫ (zeroScalarIso A Z).inv) =
      (scalarTensorHomEquiv A K Z).symm h := by
  apply (scalarTensorHomEquiv A K Z).injective
  rw [← zeroScalarIso_characteristic, ← zeroAdjunction_homEquiv]
  simp only [Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every source map commutes with this same complete zero-row comparison. -/
@[reassoc] theorem zeroScalarIso_source {A B : Original.{u} 1}
    (f : A ⟶ B) (Z : Original.{u} 1) :
    zero.map (sourceMap f Z) ≫ (zeroScalarIso A Z).hom =
      (zeroScalarIso B Z).hom ≫ innerHomPre f Z := by
  let K := zero.obj (object B Z)
  let g := ((zeroAdjunction B).homEquiv K Z).symm (𝟙 K)
  have hg : zeroTranspose B K Z g = 𝟙 K := by
    rw [← zeroAdjunction_homEquiv]
    exact ((zeroAdjunction B).homEquiv K Z).apply_symm_apply (𝟙 K)
  have h := zeroScalarIso_characteristic A K Z ((scalarTensor.map f).app K ≫ g)
  rw [zeroTranspose_source, hg, Category.id_comp, scalarTensorHomEquiv_source] at h
  have hB : scalarTensorHomEquiv B K Z g = (zeroScalarIso B Z).hom := by
    have h0 := zeroScalarIso_characteristic B K Z g
    rw [hg, Category.id_comp] at h0
    exact h0.symm
  rw [hB] at h
  exact h

/-- Every target map commutes with this same complete zero-row comparison. -/
@[reassoc] theorem zeroScalarIso_target (A : Original.{u} 1)
    {Z V : Original.{u} 1} (g : Z ⟶ V) :
    zero.map (targetMap A g) ≫ (zeroScalarIso A V).hom =
      (zeroScalarIso A Z).hom ≫ innerHomPost A g :=
  (zeroScalarNatIso A).hom.naturality g

end SimplicialPresheaf.OrderedJFS.OneFunctor
