/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
public import MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
public import MathlibExt.CategoryTheory.DGSourceMore.SimplexSubinterval

/-!
# All joint coherent-frame tensor coefficients

Hom simplices are first sent through the native free-linearized Moore
projection, Dold--Kan counit and good-truncation inclusion. The joint
coefficient is the actual Alexander--Whitney front/back sum, followed
by the given enriched DG tensor functor. This fixes all joint frame
Hom simplices, not just constant rows or columns.

The generic assembly of these full frame equations into a coherent
nerve tensor remains a construction request. No assertion that the
nonsymmetric point-set Gamma tensorator is a strict product functor
is used here. References: Lurie Higher Algebra Construction 1.3.1.13;
the native Alexander--Whitney source in DGSourceMore.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
open scoped Simplicial

universe u v v' v'' w
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
    {J : Type w} [EnrichedCategory SSet.{u} J]

/-- The actual DG object at a coherent frame vertex. -/
def frameObject (a : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) C)) (i : J) : C :=
  (ForgetEnrichment.to SSet.{u} (a.obj i)).underlying R

/-- Every coherent Hom simplex has its native degree -m cochain coefficient. -/
def frameCoefficient (a : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) C))
    (i j : J) (m : ℕ) (s : (i ⟶[SSet.{u}] j) _⦋m⦌) :
    DGHom R (-(m : ℤ)) (frameObject a i) (frameObject a j) := by
  let K := dgHomComplex R (frameObject a i) (frameObject a j)
  have h : (a.obj i ⟶[SSet.{u}] a.obj j) = (cochainToSSet R).obj K :=
    DGSimplicialCategory.hom_eq R (ForgetEnrichment.to SSet.{u} (a.obj i))
      (ForgetEnrichment.to SSet.{u} (a.obj j))
  have x : (simplicialModule K) _⦋m⦌ := by
    have x' := (a.map i j).app (op ⦋m⦌) s
    rw [h, cochainToSSet_obj] at x'
    exact x'
  exact (coefficientMap K m).hom x

/-- The source Alexander--Whitney joint tensor sum in the native total Hom degree. -/
def jointCoefficient {D : Type v'} [DGCategory R D]
    (a : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) C))
    (b : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) D))
    (i j : J) (m : ℕ) (s : (i ⟶[SSet.{u}] j) _⦋m⦌) :
    DGHom R (-(m : ℤ)) (frameObject a i, frameObject b i) (frameObject a j, frameObject b j) :=
  ∑ r : Fin (m + 1),
    dgTensorHom R (C := C) (D := D)
      (X := (frameObject a i, frameObject b i)) (Y := (frameObject a j, frameObject b j))
      (p := -((r : ℕ) : ℤ)) (q := -((m - (r : ℕ) : ℕ) : ℤ)) (n := -(m : ℤ))
      (frameCoefficient a i j (r : ℕ)
        ((i ⟶[SSet.{u}] j).map (SimplexCategory.subinterval 0 (r : ℕ) (by omega)).op s))
      (frameCoefficient b i j (m - (r : ℕ))
        ((i ⟶[SSet.{u}] j).map
          (SimplexCategory.subinterval (r : ℕ) (m - (r : ℕ)) (by omega)).op s))
      (by omega)

/-- Complete joint frame normalization fixes every vertex and every normalized Hom coefficient. -/
structure JointFrameModel {D : Type v'} [DGCategory R D] {E : Type v''} [DGCategory R E]
    (T : EnrichedFunctor (Cochains R) (C × D) E)
    (a : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) C))
    (b : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) D))
    (c : EnrichedFunctor SSet.{u} J (DGSimplicial (k := R) E)) where
  object_eq : ∀ i : J, frameObject c i = T.obj (frameObject a i, frameObject b i)
  coefficient_eq : ∀ (i j : J) (m : ℕ) (s : (i ⟶[SSet.{u}] j) _⦋m⦌),
    HEq (frameCoefficient c i j m s) (T.dgMap (-(m : ℤ)) (jointCoefficient a b i j m s))

end MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames
