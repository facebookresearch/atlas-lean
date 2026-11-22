/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoAdditive
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoArrowExactness
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryIntegerPuppeComplex

/-!
# Ordinary stable homotopy groups and Puppe exactness

These clients use the constructed preadditive structure and biproducts, the original
ordinary suspension-loop adjunction, and the represented and integer Puppe sequences.
Stability is an explicit equivalence hypothesis on the specified ordinary suspension.
The integer sequence retains the original arrow, zero object and limiting fibre cone;
the topological comparison retains the pointed CGWH enrichment and model action.
-/

set_option autoImplicit false

noncomputable section

universe w u v uT

open CategoryTheory Limits HomotopicalAlgebra

namespace MathlibExtTest.OrdinaryStablePuppeAPI

section Stable

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "H" => toHomotopyCategory C
local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)

example : Preadditive (HomotopyCategory C) :=
  OrdinaryStableHoPreadditive.preadditive g

example {X Y T : HomotopyCategory C} (f h : X ⟶ Y) (k : Y ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (f + h) ≫ k = f ≫ k + h ≫ k := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.add_comp X Y T f h k

example :
    letI := OrdinaryStableHoPreadditive.preadditive g
    HasFiniteBiproducts (HomotopyCategory C) :=
  OrdinaryStableHoBiproducts.hasFiniteBiproducts g

example {Y Z T : HomotopyCategory C} (f : Y ⟶ T) (h : Z ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (OrdinaryStableHoBiproducts.bicone g Y Z).inl ≫
        OrdinaryStableHoBiproducts.desc g f h = f ∧
      (OrdinaryStableHoBiproducts.bicone g Y Z).inr ≫
        OrdinaryStableHoBiproducts.desc g f h = h := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact ⟨OrdinaryStableHoBiproducts.inl_desc g f h,
    OrdinaryStableHoBiproducts.inr_desc g f h⟩

example (X Y : HomotopyCategory C) (f h : (Σ).obj X ⟶ Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OrdinaryStableHoAdditive.homAddEquiv g X Y (f + h) =
      OrdinaryStableHoAdditive.homAddEquiv g X Y f +
        OrdinaryStableHoAdditive.homAddEquiv g X Y h := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact (OrdinaryStableHoAdditive.homAddEquiv g X Y).map_add f h

variable (Z : C) (hZ : IsZero Z)

example {F G : Arrow C} (a : F ⟶ G) :
    OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a ≫
        OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ G =
      OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫
        (Σ).map ((H).map a.left) :=
  OrdinaryStablePuppeConnecting.boundary_naturality g Z hZ a

example {F G : Arrow C} (a : F ⟶ G) {E E' : HomotopyCategory C}
    (t : E ⟶ E') (h : (Σ).obj ((H).obj G.left) ⟶ E) :
    OrdinaryStablePuppeConnecting.connecting g Z hZ F E'
        ((Σ).map ((H).map a.left) ≫ h ≫ t) =
      OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a ≫
        OrdinaryStablePuppeConnecting.connecting g Z hZ G E h ≫ t := by
  rw [OrdinaryStablePuppeConnecting.connecting_source,
    OrdinaryStablePuppeConnecting.connecting_target]

example {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C)
    (h : OrdinaryStableHoArrowTriangle.cofiber g Z hZ f ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OrdinaryStableHoArrowTriangle.inclusion g Z hZ f ≫ h = 0 →
      ∃ k : (Σ).obj X ⟶ E,
        OrdinaryStableHoArrowTriangle.boundary g Z hZ f ≫ k = h := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact (OrdinaryStableHoArrowExactness.exact_at_cofiber g Z hZ f E h).mpr

example {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (OrdinaryStableHoArrowExactness.restrict g Z hZ f E)
        (OrdinaryStableHoArrowExactness.input g f E) ∧
      Function.Exact (OrdinaryStableHoArrowExactness.connecting g Z hZ f E)
        (OrdinaryStableHoArrowExactness.restrict g Z hZ f E) ∧
      Function.Exact (OrdinaryStableHoArrowExactness.suspendedInput g f E)
        (OrdinaryStableHoArrowExactness.connecting g Z hZ f E) :=
  OrdinaryStableHoArrowExactness.represented_long_exact g Z hZ f E

section IntegerFibre

variable {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

example (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ∀ n : ℤ,
      Function.Exact
          (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T)
          (OriginalOrdinaryIntegerPuppePositions.firstLeg g Z hZ f s n T) ∧
        Function.Exact
          (OriginalOrdinaryIntegerPuppePositions.firstLeg g Z hZ f s n T)
          (OriginalOrdinaryIntegerPuppePositions.input g f n T) ∧
        Function.Exact (OriginalOrdinaryIntegerPuppePositions.input g f (n + 1) T)
          (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T) :=
  OriginalOrdinaryIntegerPuppeExactSequence.integer_long_exact g Z hZ f s hs T

example (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (OriginalOrdinaryIntegerPuppeComplex.coefficientComplex g Z hZ f s hs T).d
        (.target (n + 1)) (.fibre n) =
      AddCommGrpCat.ofHom
        (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T) :=
  OriginalOrdinaryIntegerPuppeComplex.coefficientComplex_d_boundary_successor
    g Z hZ f s hs n T

example (T : HomotopyCategory C)
    (i : OriginalOrdinaryIntegerPuppeComplex.Position) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (OriginalOrdinaryIntegerPuppeComplex.coefficientComplex g Z hZ f s hs T).Acyclic ∧
      IsZero ((OriginalOrdinaryIntegerPuppeComplex.coefficientComplex
        g Z hZ f s hs T).homology i) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact ⟨OriginalOrdinaryIntegerPuppeComplex.coefficientComplex_acyclic
      g Z hZ f s hs T,
    OriginalOrdinaryIntegerPuppeComplex.coefficientComplex_homology_zero
      g Z hZ f s hs T i⟩

end IntegerFibre

end Stable

section TopologicalComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [EnrichedOrdinaryCategory PointedCGWH.{uT, v} C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  (a : DerivedSuspensionLoopAdjunction.Topological.Action (C := C))
  (d : GeneratedFunctorialReplacements.Data (C := C))

example :
    DerivedSuspensionLoopAdjunction.suspension d ≅
      DerivedSuspensionLoopAdjunction.Topological.sphereOneDerivedSuspension a d :=
  DerivedSuspensionLoopAdjunction.Topological.suspensionSphereOneComparison a d

example :
    DerivedSuspensionLoopAdjunction.loops d ≅
      DerivedSuspensionLoopAdjunction.Topological.sphereOneDerivedLoops a d :=
  DerivedSuspensionLoopAdjunction.Topological.loopsSphereOneComparison a d

end TopologicalComparison

end MathlibExtTest.OrdinaryStablePuppeAPI
