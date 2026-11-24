/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Actual balanced derived coefficient-module tensors

The coefficient algebra is the native enriched endomorphism algebra
of the one coefficient object. Module action is fixed on every
homogeneous coefficient by the actual right DG module functor.
The right action is obtained by the native cochain braiding.

The balanced tensor is the literal coequalizer of the two module
actions. Cofibrant inputs give the derived tensor model. Output
module action and every homogeneous functor map are fixed on the
actual quotient generators, including the native Koszul sign.
No independent tensor object or pairing is named.

References: PTVV arXiv:1111.3209v4, §2.1; Keller, Deriving DG
categories, §§2 and 6. The source DG module, cochain tensor and
localization primitives remain in their attributed native modules.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open CochainComplex.HomComplex

universe u
variable {R : Type u} [CommRing R] (C : DGCat R) (o : C)

/-- The coefficient algebra retains the actual enriched unit and multiplication. -/
abbrev coefficientAlgebra : DGAlgebra R := endomorphismAlgebra (k := R) o

/-- Coefficients are the actual module value at the coefficient object. -/
abbrev value (M : RightModule R C) : Cochains R := M.toEnrichedFunctor.obj (op o)

/-- The commutative coefficient condition is the native cochain braiding equation. -/
def IsCommutativeCoefficient : Prop :=
  (β_ (coefficientAlgebra C o).X (coefficientAlgebra C o).X).hom ≫
    MonObj.mul (X := (coefficientAlgebra C o).X) =
      MonObj.mul (X := (coefficientAlgebra C o).X)

/-- An action model has the actual DG module action on every homogeneous generator. -/
structure ActionModel (M : RightModule R C) where
  map : (coefficientAlgebra C o).X ⊗ value C o M ⟶ value C o M
  normalized : ∀ (p q n : ℤ) (h : p + q = n)
    (a : DGHom R p o o) (m : (value C o M).X q),
    ((HomologicalComplex.ιTensorObj (coefficientAlgebra C o).X (value C o M) p q n h) ≫
      map.f n).hom (TensorProduct.tmul R a m) =
      ((M.toEnrichedFunctor.dgMap p (X := op o) (Y := op o) a :
        Cochain (value C o M) (value C o M) p).v q n (by omega)).hom m

/-- The right action uses the native Koszul braiding, with no separate sign choice. -/
def rightAction {M : RightModule R C} (L : ActionModel C o M) :
    value C o M ⊗ (coefficientAlgebra C o).X ⟶ value C o M :=
  (β_ (value C o M) (coefficientAlgebra C o).X).hom ≫ L.map

/-- The first actual balanced relation acts on the first module factor. -/
def relationLeft {M N : RightModule R C} (L : ActionModel C o M) :
    (value C o M ⊗ (coefficientAlgebra C o).X) ⊗ value C o N ⟶
      value C o M ⊗ value C o N := rightAction C o L ⊗ₘ 𝟙 _

/-- The second actual balanced relation acts on the second module factor. -/
def relationRight {M N : RightModule R C} (L : ActionModel C o N) :
    (value C o M ⊗ (coefficientAlgebra C o).X) ⊗ value C o N ⟶
      value C o M ⊗ value C o N :=
  (α_ (value C o M) (coefficientAlgebra C o).X (value C o N)).hom ≫ (𝟙 _ ⊗ₘ L.map)

/-- The coequalizer of the two coefficient actions on `M ⊗ N`. It is the balanced tensor
`M ⊗_A N` when the coefficient algebra `A` is graded-commutative (`IsCommutativeCoefficient`),
since the action of `A` on the second right module is then also a left action. Without this
hypothesis the coequalizer need not compute `M ⊗_A N`; `DerivedTensorModel` requires it. -/
def balancedTensor {M N : RightModule R C}
    (L : ActionModel C o M) (K : ActionModel C o N) : Cochains R :=
  coequalizer (relationLeft C o (N := N) L) (relationRight C o (M := M) K)

/-- The actual quotient map fixes every tensor generator. -/
def quotientMap {M N : RightModule R C}
    (L : ActionModel C o M) (K : ActionModel C o N) :
    value C o M ⊗ value C o N ⟶ balancedTensor C o L K :=
  coequalizer.π _ _

/-- Homogeneous pure generators are sent through the native total tensor and quotient. -/
def generator {M N : RightModule R C}
    (L : ActionModel C o M) (K : ActionModel C o N) {p q n : ℤ} (h : p + q = n)
    (m : (value C o M).X p) (v : (value C o N).X q) : (balancedTensor C o L K).X n :=
  ((HomologicalComplex.ιTensorObj (value C o M) (value C o N) p q n h) ≫
    (quotientMap C o L K).f n).hom (TensorProduct.tmul R m v)

/-- The quotient satisfies exactly the native balancing equation. -/
theorem quotient_balance {M N : RightModule R C}
    (L : ActionModel C o M) (K : ActionModel C o N) :
    relationLeft C o (N := N) L ≫ quotientMap C o L K =
      relationRight C o (M := M) K ≫ quotientMap C o L K := coequalizer.condition _ _

/-- Output module values and their coefficient action are fixed on all quotient generators. -/
structure BalancedModuleModel (M N P : RightModule R C)
    (L : ActionModel C o M) (K : ActionModel C o N) where
  comparison : value C o P ≅ balancedTensor C o L K
  action : ∀ (a p q n t : ℤ) (h : p + q = n) (ha : n + a = t)
    (b : DGHom R a o o) (m : (value C o M).X p) (v : (value C o N).X q),
    (comparison.hom.f t).hom
      (((P.toEnrichedFunctor.dgMap a (X := op o) (Y := op o) b :
        Cochain (value C o P) (value C o P) a).v n t ha).hom
          ((comparison.inv.f n).hom (generator C o L K h m v))) =
    generator C o L K (show (p + a) + q = t by omega)
      (((M.toEnrichedFunctor.dgMap a (X := op o) (Y := op o) b :
        Cochain (value C o M) (value C o M) a).v p (p + a) rfl).hom m) v

/-- The actual homogeneous component of a module morphism at the coefficient object. -/
def mapValue {M N : RightModule R C} {r p q : ℤ} (f : DGHom R r M N) (h : p + r = q)
    (m : (value C o M).X p) : (value C o N).X q :=
  ((DGFunctor.dgApp R r (op o) f : Cochain (value C o M) (value C o N) r).v p q h).hom m

/-- A derived tensor enhancement keeps the actual quotient in every object,
and the source cochain tensor sign in every homogeneous map. The coefficient algebra is
graded-commutative, so that the quotient is the balanced tensor of right modules. -/
structure DerivedTensorModel where
  action : ∀ M : RightModule R C, ActionModel C o M
  functor : EnrichedFunctor (Cochains R)
    ((DGDerivedModules R C) × (DGDerivedModules R C)) (DGDerivedModules R C)
  value : ∀ M N : DGDerivedModules R C,
    BalancedModuleModel C o M.obj N.obj (functor.obj (M, N)).obj (action M.obj) (action N.obj)
  map_normalized : ∀ (M N M' N' : DGDerivedModules R C)
    (r s t p q n : ℤ) (h : r + s = t) (hpq : p + q = n)
    (f : DGHom R r M M') (g : DGHom R s N N')
    (m : (DerivedCoefficientTensorModels.value C o M.obj).X p)
    (v : (DerivedCoefficientTensorModels.value C o N.obj).X q),
    ((value M' N').comparison.hom.f (n + t)).hom
      (mapValue C o (M := (functor.obj (M, N)).obj) (N := (functor.obj (M', N')).obj)
        (functor.dgMap t
          ((HomologicalComplex.ιTensorObj (dgHomComplex R M M') (dgHomComplex R N N')
            r s t h).hom (TensorProduct.tmul R f g))) rfl
          (((value M N).comparison.inv.f n).hom
            (generator C o (action M.obj) (action N.obj) hpq m v))) =
    (s * p).negOnePow •
      generator C o (action M'.obj) (action N'.obj)
        (show (p + r) + (q + s) = n + t by omega)
        (mapValue C o (M := M.obj) (N := M'.obj) f rfl m)
        (mapValue C o (M := N.obj) (N := N'.obj) g rfl v)
  /-- The coefficient algebra is graded-commutative (see `balancedTensor`). -/
  commutative : IsCommutativeCoefficient C o

end MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
