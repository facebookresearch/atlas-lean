/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiFiniteComplexPresentations
public import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization
public import MathlibExt.AlgebraicGeometry.StackBundleCones
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Actual infinitesimal marked-curve extensions and source presentations

Source objects are actual marked nodal curve families over A plus I,
with the entire Cartesian reduction and each marking fixed. Their arrows
are actual curve isomorphisms over the extension preserving that reduction.
The source matrix presents this full groupoid on every A-module, with
coefficient maps realized by native Cartesian curve base changes.
Source: Jun Li arXiv:math/0110113v1, equations1.15--1.17, printed pp13--14;
the source Ext is Ext(Ω_C/A(D), I), including moving marked sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiMarkedCurveExtensions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MarkedCurveStabilization StackBundleCones LiFiniteComplexPresentations
open scoped TensorProduct

variable (A : Type) [CommRing A]

def unopRing : Aᵐᵒᵖ →+* A where
  toFun := MulOpposite.unop
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' x y := mul_comm y.unop x.unop

local instance oppositeModule (I : ModuleCat.{0} A) : Module Aᵐᵒᵖ I :=
  Module.compHom I (unopRing A)

local instance centralModule (I : ModuleCat.{0} A) : IsCentralScalar A I where
  op_smul_eq_smul _ _ := rfl

local instance oppositeComm (I : ModuleCat.{0} A) : SMulCommClass A Aᵐᵒᵖ I where
  smul_comm r s x := by
    change r • (s.unop • x) = s.unop • (r • x)
    exact smul_comm _ _ _

local instance oppositeTower (I : ModuleCat.{0} A) : IsScalarTower A Aᵐᵒᵖ I where
  smul_assoc r s x := by
    change (r * s.unop) • x = r • (s.unop • x)
    exact mul_smul _ _ _

def reduction (I : ModuleCat.{0} A) : Spec (.of A) ⟶ Spec (.of (TrivSqZeroExt A I)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A I).toRingHom)

def baseMap {I N : ModuleCat.{0} A} (u : I ⟶ N) :
    Spec (.of (TrivSqZeroExt A N)) ⟶ Spec (.of (TrivSqZeroExt A I)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map u.hom).toRingHom)

variable {A} {n g : ℕ} (F : MarkedFamily (Spec (.of A)) n g)

structure Family (I : ModuleCat.{0} A) where
  curve : MarkedFamily (Spec (.of (TrivSqZeroExt A I))) n g
  reduction : F.X ⟶ curve.X
  cartesian : IsPullback reduction F.π curve.π (LiMarkedCurveExtensions.reduction A I)
  markings : ∀ i : Fin n, F.marking i ≫ reduction =
    LiMarkedCurveExtensions.reduction A I ≫ curve.marking i

structure FamilyIso {I : ModuleCat.{0} A} (E H : Family F I) where
  iso : E.curve.X ≅ H.curve.X
  over : iso.hom ≫ H.curve.π = E.curve.π
  markings : ∀ i : Fin n, E.curve.marking i ≫ iso.hom = H.curve.marking i
  reduction : E.reduction ≫ iso.hom = H.reduction

@[ext] theorem FamilyIso.ext {I : ModuleCat.{0} A} {E H : Family F I} (e h : FamilyIso F E H)
    (same : e.iso = h.iso) : e = h := by cases e; cases h; cases same; rfl

instance familyGroupoid (I : ModuleCat.{0} A) : Groupoid (Family F I) where
  Hom E H := FamilyIso F E H
  id E := ⟨Iso.refl _, by simp, by simp, by simp⟩
  comp e h := ⟨e.iso ≪≫ h.iso, by simp [Category.assoc, h.over, e.over],
    by intro i; simp [← Category.assoc, e.markings, h.markings],
    by simp [← Category.assoc, e.reduction, h.reduction]⟩
  inv e := ⟨e.iso.symm, by rw [← e.over]; simp,
    by intro i; rw [← e.markings]; simp, by rw [← e.reduction]; simp⟩
  id_comp e := by apply FamilyIso.ext; simp
  comp_id e := by apply FamilyIso.ext; simp
  assoc e h j := by apply FamilyIso.ext; simp
  inv_comp e := by apply FamilyIso.ext; simp
  comp_inv e := by apply FamilyIso.ext; simp

structure BaseChange {I N : ModuleCat.{0} A} (u : I ⟶ N) (E : Family F I) (H : Family F N) where
  map : H.curve.X ⟶ E.curve.X
  cartesian : IsPullback map H.curve.π E.curve.π (baseMap A u)
  reduction : H.reduction ≫ map = E.reduction
  markings : ∀ i : Fin n, H.curve.marking i ≫ map = baseMap A u ≫ E.curve.marking i

variable (P : Matrix A)

theorem tensor_natural {I N : ModuleCat.{0} A} (u : I ⟶ N) :
    tensorDifferential P I ≫ rightCoefficientMap P I u.hom =
      leftCoefficientMap P I u.hom ≫ tensorDifferential P N := by
  apply ModuleCat.hom_ext
  change (TensorProduct.map LinearMap.id u.hom).comp (TensorProduct.map P.differential LinearMap.id) =
    (TensorProduct.map P.differential LinearMap.id).comp (TensorProduct.map LinearMap.id u.hom)
  apply TensorProduct.ext'
  intro x y
  simp

def quotientReindex {I N : ModuleCat.{0} A} (u : I ⟶ N) :
    AdditiveQuotient (tensorDifferential P I).hom ⥤ AdditiveQuotient (tensorDifferential P N).hom where
  obj x := ⟨rightCoefficientMap P I u.hom x.value⟩
  map {x y} e :=
    { translation := leftCoefficientMap P I u.hom e.translation
      relation := by
        change rightCoefficientMap P I u.hom y.value =
          rightCoefficientMap P I u.hom x.value + tensorDifferential P N (leftCoefficientMap P I u.hom e.translation)
        rw [e.relation, map_add]
        exact congrArg (fun z => rightCoefficientMap P I u.hom x.value + z)
          (ConcreteCategory.congr_hom (tensor_natural P u) e.translation) }
  map_id x := by apply AdditiveQuotient.hom_ext; exact map_zero _
  map_comp e h := by apply AdditiveQuotient.hom_ext; exact map_add _ _ _

structure Classification where
  matrix : Matrix A
  functor : ∀ I : ModuleCat.{0} A,
    Family F I ⥤ AdditiveQuotient (tensorDifferential matrix I).hom
  equivalence : ∀ I : ModuleCat.{0} A, (functor I).IsEquivalence
  reindex : ∀ {I N : ModuleCat.{0} A}, (I ⟶ N) → (Family F I ⥤ Family F N)
  baseChange : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) (E : Family F I),
    BaseChange F u E ((reindex u).obj E)
  arrows : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) {E H : Family F I} (e : E ⟶ H),
    ((reindex u).map e).iso.hom ≫ (baseChange u H).map =
      (baseChange u E).map ≫ e.iso.hom
  naturality : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    reindex u ⋙ functor N ≅ functor I ⋙ quotientReindex matrix u
  identity : ∀ I : ModuleCat.{0} A, reindex (𝟙 I) ≅ 𝟭 (Family F I)
  identity_map : ∀ (I : ModuleCat.{0} A) (E : Family F I),
    (baseChange (𝟙 I) E).map = ((identity I).hom.app E).iso.hom
  composition : ∀ {I N Q : ModuleCat.{0} A} (u : I ⟶ N) (v : N ⟶ Q),
    reindex u ⋙ reindex v ≅ reindex (u ≫ v)
  composition_map : ∀ {I N Q : ModuleCat.{0} A} (u : I ⟶ N) (v : N ⟶ Q) (E : Family F I),
    ((composition u v).hom.app E).iso.hom ≫ (baseChange (u ≫ v) E).map =
      (baseChange v ((reindex u).obj E)).map ≫ (baseChange u E).map

end MathlibExt.AlgebraicGeometry.LiMarkedCurveExtensions
