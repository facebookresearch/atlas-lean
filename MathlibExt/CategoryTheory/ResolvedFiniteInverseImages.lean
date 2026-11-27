/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Finite inverse images before the derived inverse limit

The source tower is first carried through its actual inverse-image
functor. Mathlib's native injective resolution is then taken in the
WHOLE diagram category. Evaluating that resolution supplies compatible
finite resolved cochains and their actual transition maps.

The Milnor fibre uses these resolved cochains. Its qualification retains
K-injectivity of the evaluated terms and of their native cochain product.
Thus the formula retains the derived product required in a sheaf category.
It does not commute an inverse-image functor with a derived limit.

References: Bhatt--Morrow--Scholze, arXiv:1802.03261v2, Remark 10.3;
Scholze, arXiv:1205.3463v2, Section 8; native Mathlib injective resolutions,
K-injective complexes and complex-of-functors evaluation, Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.ResolvedFiniteInverseImages

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A]
  {C : Type u₂} [Category.{v₂} C] [Abelian C]
  (ν : A ⥤ C) (T : ℕᵒᵖ ⥤ A)

/-- Apply the original inverse image at every finite level. -/
def finiteInverseImages : ℕᵒᵖ ⥤ C := T ⋙ ν

variable [EnoughInjectives (ℕᵒᵖ ⥤ C)]

/-- The native resolution belongs to the complete finite-image diagram. -/
def nativeResolution : InjectiveResolution (finiteInverseImages ν T) :=
  injectiveResolution (finiteInverseImages ν T)

/-- The compatible resolved cochains are native evaluation of that resolution. -/
def resolved : ℕᵒᵖ ⥤ CochainComplex C ℤ :=
  (nativeResolution ν T).cochainComplex.asFunctor

/-- The unresolved finite cochains have their original objects in degree zero. -/
def finiteCochains : ℕᵒᵖ ⥤ CochainComplex C ℤ :=
  ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ C) 0).obj
    (finiteInverseImages ν T)).asFunctor

/-- Every finite unit comes from the same native diagram resolution. -/
def unit : finiteCochains ν T ⟶ resolved ν T :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (nativeResolution ν T).ι'

instance finiteUnit_quasiIso (n : ℕ) : QuasiIso ((unit ν T).app (op n)) := by
  change QuasiIso ((((evaluation (ℕᵒᵖ) C).obj (op n)).mapHomologicalComplex
    (.up ℤ)).map (nativeResolution ν T).ι')
  infer_instance

variable [HasLimitsOfShape (Discrete ℕ) C]

abbrev resolvedProduct : CochainComplex C ℤ :=
  ∏ᶜ (fun n : ℕ => (resolved ν T).obj (op n))

/-- Source qualification of the actual resolved finite cochains and product. -/
structure Qualification where
  componentKInjective : ∀ n : ℕ, ((resolved ν T).obj (op n)).IsKInjective
  productKInjective : (resolvedProduct ν T).IsKInjective

/-- The transition is the original arrow of the resolved inverse system. -/
def transition (n : ℕ) :
    (resolved ν T).obj (op (n + 1)) ⟶ (resolved ν T).obj (op n) :=
  (resolved ν T).map (homOfLE (Nat.le_succ n)).op

/-- The actual Milnor difference on the derived-product model. -/
def difference : resolvedProduct ν T ⟶ resolvedProduct ν T :=
  Pi.lift (fun n : ℕ =>
    Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) n -
      Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) (n + 1) ≫ transition ν T n)

/-- The resolved Milnor fibre retains all finite levels and their transitions. -/
def limitComplex (_Q : Qualification ν T) : CochainComplex C ℤ :=
  CochainComplex.mappingCocone (difference ν T)

/-- The qualified derived inverse-limit object. -/
def derivedLimit (Q : Qualification ν T) : DerivedCategory C :=
  DerivedCategory.Q.obj (limitComplex ν T Q)

/-- Projection to the original finite inverse image uses its native resolution unit. -/
def finiteProjection (Q : Qualification ν T) (n : ℕ) :
    derivedLimit ν T Q ⟶ DerivedCategory.Q.obj ((finiteCochains ν T).obj (op n)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst (difference ν T) ≫
      Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) n) ≫
    inv (DerivedCategory.Q.map ((unit ν T).app (op n)))

end MathlibExt.CategoryTheory.ResolvedFiniteInverseImages
