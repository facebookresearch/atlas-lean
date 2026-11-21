/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.GeometricChow
public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage
public import MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
public import MathlibExt.AlgebraicGeometry.VerdierBetti

/-!
# A characterized Betti cycle-realization interface

Cycle groups and rational relations are the concrete length-weighted
geometric Chow presentation. Borel–Moore groups are the actual derived Hom
groups of a compact-support dualizing representation. The proper map in the
normalization is obtained from the actual compact-support pullback, not a
separately supplied trace operator.

`CycleMap` and `CycleRealization` specify the input required by subsequent
geometry. Their global construction is not asserted here: it is a Wanted
request. The compatible purity family is selected with that construction;
the normalization does not quantify over independently rescaled purities.
No canonical complex-orientation choice is claimed by this interface.

Reference: W. Fulton, *Intersection Theory*, §19.1, cycle classes in
Borel–Moore homology and their compatibility with proper maps and products.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BettiCycleRealization

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification
open CompactSupportBetti VerdierBetti ProperBettiFunctoriality
open DeCataldoMiglioriniDecompositionWanted (IsProjectiveOverC)

attribute [local instance] HasDerivedCategory.standard

/-- Push the actual length-weighted fundamental cycle to the ambient scheme. -/
def pushedFundamentalCycle {X Y : ComplexScheme} (f : X ⟶ Y)
    [IsProper f.left] [IsNoetherian X.left] (r : ℕ) :
    GeometricChow.CycleGroup Y.left r :=
  GeometricChow.dimensionPart Y.left r
    (AlgebraicCycle.map f.left Order.height Order.height
      (GeometricChow.fundamentalCycle X.left))

/-- The actual scheme-theoretic intersection of two closed subschemes. -/
def intersection {X Y Z : ComplexScheme} (i : Y ⟶ X) (j : Z ⟶ X) :
    ComplexScheme :=
  Over.mk (pullback.fst i.left j.left ≫ Y.hom)

/-- Its induced map to the actual ambient scheme. -/
def intersectionMap {X Y Z : ComplexScheme} (i : Y ⟶ X) (j : Z ⟶ X) :
    intersection i j ⟶ X :=
  Over.homMk (pullback.fst i.left j.left ≫ i.left) (by
    simp [intersection, Category.assoc, i.w])

/-- The actual intersection map is a closed immersion. -/
instance intersectionMap_isClosedImmersion {X Y Z : ComplexScheme}
    (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left] :
    IsClosedImmersion (intersectionMap i j).left :=
  inferInstanceAs
    (IsClosedImmersion (pullback.fst i.left j.left ≫ i.left))

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X],
    DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))

/-- Actual Chow-to-Borel–Moore maps normalized on smooth proper presentations.
This is specified input data. Existence is a separate Wanted request. -/
structure CycleMap where
  /-- A compatible selected purity, relative to which fundamental classes
  and their traces are interpreted. -/
  purity : ∀ (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom],
    IsProjectiveOverC X →
      ((D X).obj ≅
        (BettiRealization.rationalUnit (space X))⟦(2 * d : ℤ)⟧)
  /-- Rational cycle realization on the actual projective quotient by fibre
  relations. Proper projective resolutions normalize every such cycle. -/
  cycleClass : ∀ (X : ComplexScheme) [IsComplexVariety X] [IsProper X.hom]
    (r : ℕ), IsProjectiveOverC X → GeometricChow.ChowGroup X r →ₗ[ℚ]
      BorelMoore (space X) (D X) (2 * r)
  /-- The whole smooth scheme realizes as the nonzero oriented fundamental
  morphism determined by its selected purity. -/
  fundamental_normalization : ∀ (X : ComplexScheme) [IsComplexVariety X]
    [IsNoetherian X.left] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    (hX : IsProjectiveOverC X),
    cycleClass X d hX ((GeometricChow.rationalEquivalences X d).mkQ
        (GeometricChow.fundamentalCycleOfDimension X.left d)) =
      fundamentalClass (space X) (D X) d (purity X d hX)
  /-- The map is fixed on every smooth projective proper presentation by
  the actual compact-support duality pushforward and selected purity. -/
  proper_normalization : ∀ {X Y : ComplexScheme}
    [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left] [IsProper X.hom] [IsProper Y.hom]
    [IsNoetherian X.left] (r : ℕ)
    [SmoothOfRelativeDimension r X.hom] (hX : IsProjectiveOverC X)
    (hY : IsProjectiveOverC Y),
    cycleClass Y r hY
        ((GeometricChow.rationalEquivalences Y r).mkQ
          (pushedFundamentalCycle f r)) =
      borelMoorePushforward (P f) (D X) (D Y) (2 * r)
        (fundamentalClass (space X) (D X) r (purity X r hX))

namespace CycleMap

variable {D P} (S : CycleMap D P)

/-- The ordinary Betti cohomology class determined by cycle realization and
the same selected ambient purity. The degree is the actual codimension. -/
def cohomologyClass (X : ComplexScheme) [IsComplexVariety X]
    (d r : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    (hX : IsProjectiveOverC X) :
    GeometricChow.ChowGroup X r →ₗ[ℚ]
      BettiRealization.Cohomology (space X)
        (2 * (d : ℤ) - 2 * (r : ℤ)) where
  toFun a := S.cycleClass X r hX a ≫
    (shiftFunctor (RationalDerived (space X)) (-(2 * r : ℤ))).map
      (S.purity X d hX).hom ≫
    (shiftFunctorAdd' (RationalDerived (space X)) (2 * d : ℤ)
      (-(2 * r : ℤ)) (2 * (d : ℤ) - 2 * (r : ℤ)) (by omega)).inv.app
      (BettiRealization.rationalUnit (space X))
  map_add' a b := by
    simp [Preadditive.add_comp]
  map_smul' q a := by
    simp [Linear.smul_comp]

end CycleMap

/-- Purity makes the fundamental-class morphism an actual isomorphism.
This provides a direct normalization test for every realization provider. -/
theorem fundamentalClass_isIso (Z : TopCat.{0}) (DZ : DualizingComplex Z)
    (d : ℕ) (e : DZ.obj ≅ (BettiRealization.rationalUnit Z)⟦(2 * d : ℤ)⟧) :
    IsIso (fundamentalClass Z DZ d e) := by
  unfold fundamentalClass
  infer_instance

/-- Transport a class between equal actual cohomological degrees. -/
def cohomologyCast {Z : TopCat.{0}} {n m : ℤ} (h : n = m) :
    BettiRealization.Cohomology Z n →ₗ[ℚ]
      BettiRealization.Cohomology Z m where
  toFun a := a ≫ eqToHom
    (congrArg (fun k : ℤ => (BettiRealization.rationalUnit Z)⟦k⟧) h)
  map_add' a b := by simp [Preadditive.add_comp]
  map_smul' q a := by simp [Linear.smul_comp]

/-- The ordinary product compatibility is anchored to an actual transverse
smooth closed intersection. Full singular intersection machinery is not
silently assumed. The realization itself remains a requested provider. -/
structure CycleRealization where
  /-- The selected actual cycle map and its fundamental normalizations. -/
  toCycleMap : CycleMap D P
  /-- Smooth closed intersections of expected dimension realize as the
  actual Yoneda cup product on the same ambient Betti complex. -/
  transverse_product : ∀ (X : ComplexScheme) [IsComplexVariety X]
    (d r s t : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    (hX : IsProjectiveOverC X) (Y Z : ComplexScheme)
    (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    [IsNoetherian Y.left] [IsNoetherian Z.left]
    [SmoothOfRelativeDimension r Y.hom]
    [SmoothOfRelativeDimension s Z.hom]
    [IsNoetherian (intersection i j).left]
    [SmoothOfRelativeDimension t (intersection i j).hom]
    (hDim : r + s = d + t),
    cohomologyCast (by omega)
        (BettiRealization.cup (space X)
          (toCycleMap.cohomologyClass X d r hX
            ((GeometricChow.rationalEquivalences X r).mkQ
              (pushedFundamentalCycle i r)))
          (toCycleMap.cohomologyClass X d s hX
            ((GeometricChow.rationalEquivalences X s).mkQ
              (pushedFundamentalCycle j s)))) =
      toCycleMap.cohomologyClass X d t hX
        ((GeometricChow.rationalEquivalences X t).mkQ
          (pushedFundamentalCycle (intersectionMap i j) t))

end MathlibExt.AlgebraicGeometry.BettiCycleRealization
