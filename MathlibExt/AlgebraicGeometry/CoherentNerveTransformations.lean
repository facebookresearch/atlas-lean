/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames

/-!
# Full coherent nerve realizations of actual DG transformations

The interval has exactly two objects and the actual free coefficient
Hom in degree zero for each ordered arrow. Its fixed generator is
sent to the given closed DG transformation. Cylinder maps are fixed
on every homogeneous source map. Joint coherent-frame equations then
fix every output simplex, including mixed parameter/module simplices.

Generic interval/cylinder/nerve assembly remains separate Wanted
construction work. This interface supplies no geometric equivalence,
orientation or nondegeneracy conclusion.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoherentNerveTransformations

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames
open scoped Simplicial

universe u v
variable {R : Type u} [CommRing R]

/-- The actual zero cochain module used for the unordered interval Hom. -/
def zeroComplex (R : Type u) [CommRing R] : Cochains R :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (ULift.{u} PUnit))

/-- The actual free coefficient interval, with the unique ordered-arrow generator fixed. -/
structure IntervalModel (R : Type u) [CommRing R] where
  carrier : Type v
  [dg : DGCategory R carrier]
  object : Fin 2 → carrier
  objects : Function.Bijective object
  hom : ∀ i j : Fin 2, dgHomComplex R (object i) (object j) ≅
    if i ≤ j then 𝟙_ (Cochains R) else zeroComplex R
  arrow : ∀ (i j : Fin 2), i ≤ j → DGHom R 0 (object i) (object j)
  arrow_closed : ∀ (i j : Fin 2) (h : i ≤ j), dgDifferential R 0 (arrow i j h) = 0
  arrow_value : ∀ (i j : Fin 2) (h : i ≤ j),
    HEq (((hom i j).hom.f 0).hom (arrow i j h))
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv 1)
  identity : ∀ i : Fin 2, arrow i i le_rfl = dgId R (object i)
  composition : ∀ (i j k : Fin 2) (h : i ≤ j) (h' : j ≤ k),
    dgComp R (arrow i j h) (arrow j k h') (by omega) = arrow i k (h.trans h')

attribute [instance] IntervalModel.dg

/-- A closed DG arrow gives its actual ordinary arrow in the coherent simplicial category. -/
def simplicialArrow {C : Type v} [DGCategory R C] {x y : C} (z : dgCycles R x y) :
    (ForgetEnrichment.of SSet.{u} (DGSimplicialCategory.of R x) : DGSimplicial (k := R) C) ⟶
      ForgetEnrichment.of SSet.{u} (DGSimplicialCategory.of R y) := by
  apply ForgetEnrichment.homOf SSet.{u}
  rw [DGSimplicialCategory.hom_eq, DGSimplicialCategory.underlying_of,
    DGSimplicialCategory.underlying_of]
  exact Functor.LaxMonoidal.ε (cochainToSSet R) ≫
    (cochainToSSet R).map
      (ForgetEnrichment.homTo (Cochains R) (dgClosedHomOf (C := C) R z.val z.property))

/-- Its actual nerve one-simplex fixes the complete interval parameter map. -/
def intervalParameter (I : IntervalModel.{u, v} R) :
    (Δ[1] : SSet.{max u v}) ⟶ dgNerve (k := R) I.carrier :=
  SSet.yonedaEquiv.symm
    (SimplicialNerve.edgeMk
      (simplicialArrow (R := R)
        ⟨I.arrow 0 1 (by decide), (mem_dgCycles R).mpr (I.arrow_closed 0 1 (by decide))⟩)).edge

variable {C D : Type v} [DGCategory R C] [DGCategory R D]

/-- The coherent product map has the actual identity DG tensor functor on every joint frame. -/
structure PairNerveModel where
  map : dgNerve (k := R) C ⊗ dgNerve (k := R) D ⟶ dgNerve (k := R) (C × D)
  joint : ∀ (n : SimplexCategoryᵒᵖ) (a : (dgNerve (k := R) C).obj n)
    (b : (dgNerve (k := R) D).obj n),
    JointFrameModel (EnrichedFunctor.id (Cochains R) (C × D)) a b (map.app n (a, b))

/-- Products of DG functors retain their literal tensor Hom map. -/
structure ProductDGFunctorModel {C' D' : Type v} [DGCategory R C'] [DGCategory R D']
    (F : EnrichedFunctor (Cochains R) C D) (G : EnrichedFunctor (Cochains R) C' D') where
  functor : EnrichedFunctor (Cochains R) (C × C') (D × D')
  object_eq : ∀ x : C × C', functor.obj x = (F.obj x.1, G.obj x.2)
  map_eq : ∀ x y : C × C', HEq (functor.map x y) (F.map x.1 y.1 ⊗ₘ G.map x.2 y.2)

/-- The DG swap uses exactly the native Koszul braiding of the Hom complexes. -/
structure SwapDGFunctorModel (C : Type v) [DGCategory R C] where
  functor : EnrichedFunctor (Cochains R) (C × C) (C × C)
  object_eq : ∀ x : C × C, functor.obj x = (x.2, x.1)
  map_eq : ∀ x y : C × C,
    HEq (functor.map x y)
      ((BraidedCategory.braiding (C := Cochains R)
        (dgHomComplex (C := C) R x.1 y.1) (dgHomComplex (C := C) R x.2 y.2)).hom)

/-- The DG associator is fixed on every Hom complex by the native cochain associator. -/
structure AssociatorDGFunctorModel (C : Type v) [DGCategory R C] where
  functor : EnrichedFunctor (Cochains R) ((C × C) × C) (C × (C × C))
  object_eq : ∀ x : (C × C) × C, functor.obj x = (x.1.1, (x.1.2, x.2))
  map_eq : ∀ x y : (C × C) × C,
    HEq (functor.map x y)
      ((MonoidalCategory.associator (C := Cochains R)
        (dgHomComplex (C := C) R x.1.1 y.1.1) (dgHomComplex (C := C) R x.1.2 y.1.2)
        (dgHomComplex (C := C) R x.2 y.2)).hom)

/-- A cylinder is fixed by the original functors and the actual transformation component. -/
structure CylinderModel (F G : EnrichedFunctor (Cochains R) C D)
    (η : ∀ x : C, DGHom R 0 (F.obj x) (G.obj x)) where
  interval : IntervalModel.{u, v} R
  functor : EnrichedFunctor (Cochains R) (C × interval.carrier) D
  object_zero : ∀ x : C, functor.obj (x, interval.object 0) = F.obj x
  object_one : ∀ x : C, functor.obj (x, interval.object 1) = G.obj x
  map_zero : ∀ (x y : C) (n : ℤ) (f : DGHom R n x y),
    HEq (functor.dgMap n (dgTensorHom R (C := C) (D := interval.carrier)
      (X := (x, interval.object 0)) (Y := (y, interval.object 0))
      (p := n) (q := 0) (n := n) f (interval.arrow 0 0 le_rfl) (add_zero n))) (F.dgMap n f)
  map_one : ∀ (x y : C) (n : ℤ) (f : DGHom R n x y),
    HEq (functor.dgMap n (dgTensorHom R (C := C) (D := interval.carrier)
      (X := (x, interval.object 1)) (Y := (y, interval.object 1))
      (p := n) (q := 0) (n := n) f (interval.arrow 1 1 le_rfl) (add_zero n))) (G.dgMap n f)
  map_arrow : ∀ (x y : C) (n : ℤ) (f : DGHom R n x y),
    HEq (functor.dgMap n (dgTensorHom R (C := C) (D := interval.carrier)
      (X := (x, interval.object 0)) (Y := (y, interval.object 1))
      (p := n) (q := 0) (n := n) f (interval.arrow 0 1 (by decide)) (add_zero n)))
      (dgComp R (F.dgMap n f) (η y) (add_zero n))

/-- The transformation nerve is fixed on every joint module/interval frame simplex. -/
structure NerveTransformationModel (F G : EnrichedFunctor (Cochains R) C D)
    (η : ∀ x : C, DGHom R 0 (F.obj x) (G.obj x)) where
  closed : ∀ x : C, dgDifferential R 0 (η x) = 0
  natural : ∀ (x y : C) (n : ℤ) (f : DGHom R n x y),
    dgComp R (F.dgMap n f) (η y) (add_zero n) =
      dgComp R (η x) (G.dgMap n f) (zero_add n)
  cylinder : CylinderModel F G η
  map : dgNerve (k := R) C ⊗ (Δ[1] : SSet.{max u v}) ⟶ dgNerve (k := R) D
  joint : ∀ (n : SimplexCategoryᵒᵖ) (a : (dgNerve (k := R) C).obj n) (t : (Δ[1]).obj n),
    JointFrameModel cylinder.functor a ((intervalParameter cylinder.interval).app n t)
      (map.app n (a, t))

end MathlibExt.AlgebraicGeometry.CoherentNerveTransformations
