/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDeRhamModels
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# The literal relative de Rham wedge product

The form terms and differential are the existing actual Kähler/exterior
presheaves. The product is Mathlib's exterior-power wedge at every original
open section ring. A cochain realization is fixed on every local tensor
summand, including arbitrary form elements, and on the actual scalar unit.
The unit to sheafified forms is the native sheafification adjunction unit.

References: Stacks Project, Tags 0FKM and 0FKG; Bhatt–Scholze,
arXiv:1905.08229v4, Theorem 1.8(3) and Corollary 15.4.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeDeRhamWedgeModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  _root_.AlgebraicGeometry
open AlgebraicDifferentialSheaves RelativeDeRhamModels
open scoped TensorProduct

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

abbrev Presheaves := X.left.Opensᵒᵖ ⥤ ModuleCat.{0} R

def wedge (i j : ℕ) (U : X.left.Opensᵒᵖ)
    (x : (formPresheaf R X i).obj U) (y : (formPresheaf R X j).obj U) :
    (formPresheaf R X (i + j)).obj U :=
  DirectSum.gMulLHom (X.left.presheaf.obj U)
    (fun d ↦ ⋀[X.left.presheaf.obj U]^d ((differentials R X).obj U)) x y

def rawNatComplex (D : Differential R X) : CochainComplex (Presheaves R X) ℕ :=
  CochainComplex.of (formPresheaf R X) D.d D.square

def rawComplex (D : Differential R X) : CochainComplex (Presheaves R X) ℤ :=
  (rawNatComplex R X D).extend ComplexShape.embeddingUpNat

def rawDegreeIso (D : Differential R X) (i : ℕ) :
    (rawComplex R X D).X (i : ℤ) ≅ formPresheaf R X i :=
  (rawNatComplex R X D).extendXIso ComplexShape.embeddingUpNat (by simp)

instance curriedTensor_additive : (curriedTensor (Presheaves R X)).Additive where
  map_add := by
    intro M M' f g
    apply NatTrans.ext
    funext N
    apply NatTrans.ext
    funext U
    change (f.app U + g.app U) ▷ N.obj U = f.app U ▷ N.obj U + g.app U ▷ N.obj U
    exact MonoidalPreadditive.add_whiskerRight _ _

instance curriedTensor_obj_additive (M : Presheaves R X) :
    ((curriedTensor (Presheaves R X)).obj M).Additive where
  map_add := by
    intro N N' f g
    apply NatTrans.ext
    funext U
    change M.obj U ◁ (f.app U + g.app U) = M.obj U ◁ f.app U + M.obj U ◁ g.app U
    exact MonoidalPreadditive.whiskerLeft_add _ _

def totalTensor (K L : CochainComplex (Presheaves R X) ℤ) :
    CochainComplex (Presheaves R X) ℤ :=
  HomologicalComplex.mapBifunctor K L (curriedTensor (Presheaves R X)) (.up ℤ)

def tensorMap {K L K' L' : CochainComplex (Presheaves R X) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') : totalTensor R X K L ⟶ totalTensor R X K' L' :=
  HomologicalComplex.mapBifunctorMap f g (curriedTensor (Presheaves R X)) (.up ℤ)

def product {K : CochainComplex (Presheaves R X) ℤ}
    (m : totalTensor R X K K ⟶ K) (i j : ℕ) (U : X.left.Opensᵒᵖ)
    (x : (K.X (i : ℤ)).obj U) (y : (K.X (j : ℤ)).obj U) :
      (K.X (i + j : ℕ)).obj U :=
  ((HomologicalComplex.ιMapBifunctor K K (curriedTensor (Presheaves R X))
    (.up ℤ) (i : ℤ) (j : ℤ) (i + j : ℕ)
      (by change (i : ℤ) + (j : ℤ) = (i + j : ℕ); omega) ≫
    m.f (i + j : ℕ)).app U).hom (x ⊗ₜ[R] y)

def scalarComplex : CochainComplex (Presheaves R X) ℤ :=
  (HomologicalComplex.single (Presheaves R X) (.up ℤ) 0).obj
    ((Functor.const _).obj (ModuleCat.of R R))

def scalarGenerator (U : X.left.Opensᵒᵖ) (a : R) :
    ((scalarComplex R X).X 0).obj U :=
  ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
    ((Functor.const X.left.Opensᵒᵖ).obj (ModuleCat.of R R))).inv.app U).hom a

/-- The ordinary cochain product is fixed on every actual local wedge.
This type does not assume any prismatic comparison theorem. -/
structure WedgeAssembly (D : Differential R X) where
  multiplication : totalTensor R X (rawComplex R X D) (rawComplex R X D) ⟶ rawComplex R X D
  wedge : ∀ (i j : ℕ) (U : X.left.Opensᵒᵖ)
    (x : (formPresheaf R X i).obj U) (y : (formPresheaf R X j).obj U),
    ((rawDegreeIso R X D (i + j)).hom.app U).hom
      (product R X multiplication i j U
        (((rawDegreeIso R X D i).inv.app U).hom x)
        (((rawDegreeIso R X D j).inv.app U).hom y)) =
      RelativeDeRhamWedgeModels.wedge R X i j U x y
  unit : scalarComplex R X ⟶ rawComplex R X D
  scalar : ∀ (U : X.left.Opensᵒᵖ) (a : R),
    ((rawDegreeIso R X D 0).hom.app U).hom
      (((unit.f 0).app U).hom (scalarGenerator R X U a)) =
      RelativeDeRhamModels.generator R X 0 U ((scalarMap R X).app U a) Fin.elim0

def sheafificationUnit (D : Differential R X) :
    rawNatComplex R X D ⟶ ((sheafToPresheaf (RelativeDeRhamModels.topology R X)
      (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).obj D.natComplex where
  f i := (sheafificationAdjunction (RelativeDeRhamModels.topology R X)
    (ModuleCat.{0} R)).unit.app (formPresheaf R X i)
  comm' i j _ := ((sheafificationAdjunction (RelativeDeRhamModels.topology R X)
    (ModuleCat.{0} R)).unit.naturality ((rawNatComplex R X D).d i j)).symm

end MathlibExt.AlgebraicGeometry.RelativeDeRhamWedgeModels
