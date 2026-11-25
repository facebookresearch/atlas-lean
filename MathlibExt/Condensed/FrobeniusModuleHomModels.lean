/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import MathlibExt.Condensed.SolidWeakPerfectModels

/-!
# Actual linearized phi objects and their mapping-complex model

A phi object has an actual cofibrant almost-local DG module and a
linearized equivalence from its actual coefficient-Frobenius extension.
For two objects the mapping complex is the native homotopy fibre of
the two prescribed compatibility maps. The first map precomposes the
source linearization; the second applies Frobenius and postcomposes the
target linearization. Integer enrichment keeps every original degree.

The enhancement output fixes its whole Hom complex and both components
of signed composition. Perfectness is the source weakly almost perfect
condition on the actual underlying module, not a compact-dictionary test.

Source: Mann, arXiv:2206.02022v1, Definitions 3.9.10 and 3.9.15;
Keller, Deriving DG categories, Section 1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.FrobeniusModuleHomModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
open MathlibExt.CategoryTheory.IntegerDGRestriction
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open LocalSolidCoefficientModels SolidTorsionFrobeniusModels SolidWeakPerfectModels
open CochainComplex.HomComplex

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)
  (π : Pseudouniformizer p P) (h : π.element ∣ (p : P.pair.plus))
  (M : TorsionModel p P π) (F : FrobeniusModel p P π h M)

/-- Actual cofibrant linearized Frobenius modules, including all component equivalences. -/
structure PhiObject where
  module : TorsionCategory p P π M
  linearized : ((F.localExtension p P π).obj module).obj ⟶ module.obj
  equivalence : ∀ x : M.compact.objectsᵒᵖ, QuasiIso (moduleComponent linearized x)

/-- The actual integer DG category in which every underlying module Hom is retained. -/
abbrev Underlying := IntegerDG (TorsionRing p P π) (TorsionCategory p P π M)

/-- The native category of closed morphisms in that integer enrichment. -/
abbrev ClosedUnderlying := ForgetEnrichment (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
  (Underlying p P π M)

/-- The actual integer DG coefficient-Frobenius functor. -/
def phiFunctor : EnrichedFunctor (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
    (Underlying p P π M) (Underlying p P π M) :=
  integerFunctor (coefficientFrobenius p P π h) (F.localExtension p P π)

/-- Its linearized arrow, as the actual underlying closed integer morphism. -/
def PhiObject.structureHom (X : PhiObject p P π h M F) :
    (ForgetEnrichment.of (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
      ((phiFunctor p P π h M F).obj X.module)) ⟶
    (ForgetEnrichment.of (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
      (show Underlying p P π M from X.module)) := by
  let a : DGHom (TorsionRing p P π) 0
      ((F.localExtension p P π).obj X.module) X.module := closedModuleHom X.linearized
  have ha : dgDifferential Integers.{1} 0
      (C := Underlying p P π M)
      (X := ((phiFunctor p P π h M F).obj X.module)) (Y := X.module) a = 0 := by
    rw [integer_differential]
    change dgDifferential (TorsionRing p P π) 0 (closedModuleHom X.linearized) = 0
    exact (mem_dgCycles _).mp (DGFunctor.homEquivDGCycles _ _ _ X.linearized).property
  exact dgClosedHomOf (C := Underlying p P π M) Integers.{1} a ((mem_dgCycles _).mpr ha)

/-- Compatibility by precomposition with the source linearization. -/
def compatibilityLeft (X Y : PhiObject p P π h M F) :
    dgHomComplex (C := Underlying p P π M) Integers.{1} X.module Y.module ⟶
      dgHomComplex (C := Underlying p P π M) Integers.{1}
        ((phiFunctor p P π h M F).obj X.module) Y.module :=
  ((eHomFunctor (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
    (ClosedUnderlying p P π M)).map (X.structureHom p P π h M F).op).app
      (ForgetEnrichment.of _ (show Underlying p P π M from Y.module))

/-- Compatibility by actual Frobenius and the target linearization. -/
def compatibilityRight (X Y : PhiObject p P π h M F) :
    dgHomComplex (C := Underlying p P π M) Integers.{1} X.module Y.module ⟶
      dgHomComplex (C := Underlying p P π M) Integers.{1}
        ((phiFunctor p P π h M F).obj X.module) Y.module :=
  (phiFunctor p P π h M F).map X.module Y.module ≫
    ((eHomFunctor (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
      (ClosedUnderlying p P π M)).obj (op (ForgetEnrichment.of _
        ((phiFunctor p P π h M F).obj X.module)))).map (Y.structureHom p P π h M F)

/-- The actual fibre uses the native cocone sign: d(h) = left(f)-right(f). -/
def mappingComplex (X Y : PhiObject p P π h M F) :
    CochainComplex (ModuleCat.{1} Integers.{1}) ℤ :=
  CochainComplex.mappingCocone
    (compatibilityRight p P π h M F X Y - compatibilityLeft p P π h M F X Y)

/-- The prescribed first mapping component. -/
def first (X Y : PhiObject p P π h M F) (n : ℤ) :
    (mappingComplex p P π h M F X Y).X n ⟶
      (dgHomComplex (C := Underlying p P π M) Integers.{1} X.module Y.module).X n :=
  (CochainComplex.mappingCocone.fst _).f n

/-- The actual homotopy component, retaining the source degree n-1. -/
def second (X Y : PhiObject p P π h M F) (n : ℤ) :
    (mappingComplex p P π h M F X Y).X n ⟶
      (dgHomComplex (C := Underlying p P π M) Integers.{1}
        ((phiFunctor p P π h M F).obj X.module) Y.module).X (n-1) :=
  (CochainComplex.mappingCocone.snd _).v n (n-1) (by omega)

set_option maxHeartbeats 1200000 in
/-- The enhancement is on these actual objects, with the entire native fibre Hom complex. -/
structure Enhancement where
  [category : DGCategory Integers.{1} (PhiObject p P π h M F)]
  hom_fixed : ∀ X Y, dgHomComplex Integers.{1} X Y = mappingComplex p P π h M F X Y
  identity_first : ∀ X : PhiObject p P π h M F,
    (first p P π h M F X X 0).hom (((eqToHom (hom_fixed X X)).f 0) (dgId Integers.{1} X)) =
      dgId (C := Underlying p P π M) Integers.{1} X.module
  identity_second : ∀ X : PhiObject p P π h M F,
    (second p P π h M F X X 0).hom (((eqToHom (hom_fixed X X)).f 0) (dgId Integers.{1} X)) = 0
  composition_first : ∀ (X Y Z : PhiObject p P π h M F) (i j n : ℤ)
    (a : DGHom Integers.{1} i X Y) (b : DGHom Integers.{1} j Y Z) (e : i + j = n),
    let fa := (first p P π h M F X Y i).hom (((eqToHom (hom_fixed X Y)).f i) a)
    let fb := (first p P π h M F Y Z j).hom (((eqToHom (hom_fixed Y Z)).f j) b)
    (first p P π h M F X Z n).hom
      (((eqToHom (hom_fixed X Z)).f n) (dgComp Integers.{1} a b e)) =
        dgComp (C := Underlying p P π M) Integers.{1} fa fb e
  composition_second : ∀ (X Y Z : PhiObject p P π h M F) (i j n : ℤ)
    (a : DGHom Integers.{1} i X Y) (b : DGHom Integers.{1} j Y Z) (e : i + j = n),
    let fa := (first p P π h M F X Y i).hom (((eqToHom (hom_fixed X Y)).f i) a)
    let ha := (second p P π h M F X Y i).hom (((eqToHom (hom_fixed X Y)).f i) a)
    let fb := (first p P π h M F Y Z j).hom (((eqToHom (hom_fixed Y Z)).f j) b)
    let hb := (second p P π h M F Y Z j).hom (((eqToHom (hom_fixed Y Z)).f j) b)
    (second p P π h M F X Z n).hom
      (((eqToHom (hom_fixed X Z)).f n) (dgComp Integers.{1} a b e)) =
        dgComp (C := Underlying p P π M) Integers.{1} ha fb (by omega) +
          i.negOnePow • dgComp (C := Underlying p P π M) Integers.{1}
            ((phiFunctor p P π h M F).dgMap i fa) hb (by omega)

/-- Source perfect phi objects retain the exact weakly almost perfect underlying condition. -/
def IsPerfectPhi (U : UnitInductionModel p P π M) (X : PhiObject p P π h M F) : Prop :=
  IsWeaklyAlmostPerfect p P π M U X.module

end MathlibExt.Condensed.FrobeniusModuleHomModels
