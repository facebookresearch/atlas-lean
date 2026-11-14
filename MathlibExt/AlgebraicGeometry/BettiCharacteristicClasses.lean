/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The Chern/Segre coefficient pattern follows AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Chow/GenuineChern/Segre.lean and
StacksFrontier/AlgebraicGeometry/Chow/ProjectiveBundleFormula/Formula.lean,
licensed under Apache 2.0. Modification notice: use the actual rational
Betti cup/push/pull maps, obtain Chern coefficients from the inverse of
the displayed projective-bundle map, and define Segre coefficients by
the explicit inverse-series recurrence. The global compatible theory
is an input construction requested separately, not an implemented instance.
-/

module
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.BettiGysin
public import MathlibExt.AlgebraicGeometry.BettiCycleRealization
/-!
# Concrete Betti characteristic-class constructors

The hyperplane class is the Euler class of the actual tautological line:
zero-section Gysin followed by pullback. The projective-bundle map is the
literal sum of h^i times the fixed pullbacks. Given bijectivity of this map,
Chern coefficients are the signed coefficients of its inverse applied to
h^(r+1), with c₀=1 and cᵢ=0 above the rank.

`projectiveSegre` is the coefficient recurrence for 1/c(-t), hence Segre of
the dual bundle in the quotient convention; `segre` gives 1/c(t) by the
corresponding sign. The requested theory includes the exact pushforward,
pullback, Whitney and projection formulas on these constructed classes.
There is no arbitrary class-valued assignment or law-bearing Chow ring.

References: Fulton, *Intersection Theory*, Chapters 3, 6 and §19.1; the
already completed generic algebraic formula sources credited above.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open BettiRealization BettiFunctoriality BettiGysin AlgebraicBundleGeometry
open scoped BigOperators
attribute [local instance] HasDerivedCategory.standard
variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))

variable (F : PureFamily D) {X : ComplexScheme} [IsComplexVariety X]
  (dx r : ℕ) [SmoothOfRelativeDimension dx X.hom] (E : X.left.Modules)
  (B : ProjectiveBundle X dx r E)
  (V : LineTotalSpace B.total (dx + r) B.tautological)

def hyperplane : BettiRealization.Cohomology (space B.total) 2 :=
  BettiCycleRealization.cohomologyCast (by omega)
    (cohomologyPullback (spaceMap V.zero) _
      (cohomologyPushforward (P V.zero) (D B.total) (D V.total) (dx + r) (dx + r + 1)
        (F.iso _ (dx + r)) (F.iso _ (dx + r + 1)) 0 (unitClass (space B.total))))

def cupPower (Z : TopCat.{0}) (h : BettiRealization.Cohomology Z 2) :
    (n : ℕ) → BettiRealization.Cohomology Z (2 * n)
  | 0 => unitClass Z
  | n + 1 => BettiCycleRealization.cohomologyCast (by omega) (cup Z (cupPower Z h n) h)

abbrev BundleDomain (X : ComplexScheme) (r : ℕ) (n : ℤ) :=
  (i : Fin (r + 1)) → BettiRealization.Cohomology (space X) (n - 2 * (i : ℕ))

def bundleComponent (n : ℤ) (i : Fin (r + 1)) :
    BundleDomain X r n →ₗ[ℚ] BettiRealization.Cohomology (space B.total) n :=
  BettiCycleRealization.cohomologyCast (by omega) ∘ₗ
    cupRight (space B.total) (cupPower (space B.total) (hyperplane D P F dx r E B V) i) ∘ₗ
      cohomologyPullback (spaceMap B.projection) (n - 2 * (i : ℕ)) ∘ₗ LinearMap.proj i

def bundleMap (n : ℤ) : BundleDomain X r n →ₗ[ℚ] BettiRealization.Cohomology (space B.total) n :=
  ∑ i : Fin (r + 1), bundleComponent D P F dx r E B V n i

structure ProjectiveBundleTheory where
  family : PureFamily D
  bijective : ∀ (X : ComplexScheme) [IsComplexVariety X] (dx r : ℕ)
    [SmoothOfRelativeDimension dx X.hom] (E : X.left.Modules)
    (B : ProjectiveBundle X dx r E) (V : LineTotalSpace B.total (dx + r) B.tautological) (n : ℤ),
    Function.Bijective (bundleMap D P family dx r E B V n)

variable (T : ProjectiveBundleTheory D P)

def bundleEquiv (n : ℤ) :
    BundleDomain X r n ≃ₗ[ℚ] BettiRealization.Cohomology (space B.total) n :=
  LinearEquiv.ofBijective (bundleMap D P T.family dx r E B V n) (T.bijective X dx r E B V n)

def positiveChern (i : Fin (r + 1)) :
    BettiRealization.Cohomology (space X) (2 * ((i : ℕ) + 1)) :=
  (-1 : ℚ) ^ ((i : ℕ) + 2) • BettiCycleRealization.cohomologyCast (by dsimp; omega)
    (((bundleEquiv D P dx r E B V T (2 * (r + 1))).symm
      (cupPower (space B.total) (hyperplane D P T.family dx r E B V) (r + 1)))
        ⟨r - (i : ℕ), by omega⟩)

def chern (i : ℕ) : BettiRealization.Cohomology (space X) (2 * i) :=
  if h0 : i = 0 then by subst i; exact unitClass (space X)
  else if hr : i ≤ r + 1 then
    BettiCycleRealization.cohomologyCast (by dsimp; omega)
      (positiveChern D P dx r E B V T ⟨i - 1, by omega⟩)
  else 0

def projectiveSegre : (n : ℕ) → BettiRealization.Cohomology (space X) (2 * n)
  | 0 => unitClass (space X)
  | n + 1 => ∑ i : Fin (n + 1), (-1 : ℚ) ^ ((i : ℕ) + 2) •
      BettiCycleRealization.cohomologyCast (by dsimp; omega)
        (cup (space X) (chern D P dx r E B V T ((i : ℕ) + 1))
          (projectiveSegre (n - (i : ℕ))))
termination_by n => n
decreasing_by omega

/-- Segre coefficients of the original bundle, in the 1/c(t) convention. -/
def segre (n : ℕ) : BettiRealization.Cohomology (space X) (2 * n) :=
  (-1 : ℚ) ^ n • projectiveSegre D P dx r E B V T n

def projectionCapPower (i : ℕ) (n : ℤ) (a : BettiRealization.Cohomology (space X) n) :
    BettiRealization.Cohomology (space X) (2 * (dx : ℤ) - (2 * ((dx + r) : ℤ) - (2 * i + n))) :=
  cohomologyPushforward (P B.projection) (D B.total) (D X) (dx + r) dx
    (F.iso _ (dx + r)) (F.iso _ dx) (2 * i + n)
    (cup (space B.total) (cupPower (space B.total) (hyperplane D P F dx r E B V) i)
      (cohomologyPullback (spaceMap B.projection) n a))

def whitneyCoefficient (s : ℕ) (G : X.left.Modules)
    (BG : ProjectiveBundle X dx s G)
    (VG : LineTotalSpace BG.total (dx + s) BG.tautological) (k : ℕ) :
    BettiRealization.Cohomology (space X) (2 * k) :=
  ∑ i : Fin (k + 1), BettiCycleRealization.cohomologyCast (by omega)
    (cup (space X) (chern D P dx r E B V T i)
      (chern D P dx s G BG VG T (k - (i : ℕ))))

structure CharacteristicClassTheory extends ProjectiveBundleTheory D P where
  projection_top : ∀ (X : ComplexScheme) [IsComplexVariety X] (dx r : ℕ)
    [SmoothOfRelativeDimension dx X.hom] (E : X.left.Modules)
    (B : ProjectiveBundle X dx r E) (V : LineTotalSpace B.total (dx + r) B.tautological)
    (n : ℤ) (a : BettiRealization.Cohomology (space X) n),
    BettiCycleRealization.cohomologyCast (by omega)
      (projectionCapPower D P family dx r E B V r n a) = a
  projection_lower : ∀ (X : ComplexScheme) [IsComplexVariety X] (dx r : ℕ)
    [SmoothOfRelativeDimension dx X.hom] (E : X.left.Modules)
    (B : ProjectiveBundle X dx r E) (V : LineTotalSpace B.total (dx + r) B.tautological)
    (i : ℕ) (_hi : i < r) (n : ℤ) (a : BettiRealization.Cohomology (space X) n),
    projectionCapPower D P family dx r E B V i n a = 0
  segre_pushforward : ∀ (X : ComplexScheme) [IsComplexVariety X] (dx r : ℕ)
    [SmoothOfRelativeDimension dx X.hom] (E : X.left.Modules)
    (B : ProjectiveBundle X dx r E) (V : LineTotalSpace B.total (dx + r) B.tautological) (n : ℕ),
    BettiCycleRealization.cohomologyCast (by omega)
      (projectionCapPower D P family dx r E B V (r + n) 0 (unitClass (space X))) =
        projectiveSegre D P dx r E B V toProjectiveBundleTheory n

  pullback_chern : ∀ (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (dx dy r : ℕ) [SmoothOfRelativeDimension dx X.hom] [SmoothOfRelativeDimension dy Y.hom]
    (E : X.left.Modules) (E' : Y.left.Modules)
    (B : ProjectiveBundle X dx r E) (B' : ProjectiveBundle Y dy r E')
    (V : LineTotalSpace B.total (dx + r) B.tautological)
    (V' : LineTotalSpace B'.total (dy + r) B'.tautological)
    (f : Y ⟶ X) (_e : (Scheme.Modules.pullback f.left).obj E ≅ E') (i : ℕ),
    cohomologyPullback (spaceMap f) (2 * i)
      (chern D P dx r E B V toProjectiveBundleTheory i) =
        chern D P dy r E' B' V' toProjectiveBundleTheory i
  whitney : ∀ (X : ComplexScheme) [IsComplexVariety X] (dx r s t : ℕ)
    [SmoothOfRelativeDimension dx X.hom] (E G H : X.left.Modules)
    (BE : ProjectiveBundle X dx r E) (BG : ProjectiveBundle X dx s G)
    (BH : ProjectiveBundle X dx t H)
    (VE : LineTotalSpace BE.total (dx + r) BE.tautological)
    (VG : LineTotalSpace BG.total (dx + s) BG.tautological)
    (VH : LineTotalSpace BH.total (dx + t) BH.tautological)
    (u : E ⟶ H) (v : H ⟶ G) (w : u ≫ v = 0)
    (_ranks : t + 1 = (r + 1) + (s + 1))
    (_exact : (ShortComplex.mk u v w).ShortExact) (k : ℕ),
    chern D P dx t H BH VH toProjectiveBundleTheory k =
      whitneyCoefficient D P dx r E BE VE toProjectiveBundleTheory s G BG VG k
  projection_formula : ∀ (X : ComplexScheme) [IsComplexVariety X] (dx r : ℕ)
    [SmoothOfRelativeDimension dx X.hom] (E : X.left.Modules)
    (B : ProjectiveBundle X dx r E)
    (i j : ℤ) (a : BettiRealization.Cohomology (space X) i)
    (b : BettiRealization.Cohomology (space B.total) j),
    BettiCycleRealization.cohomologyCast (by omega)
      (cohomologyPushforward (P B.projection) (D B.total) (D X) (dx + r) dx
        (family.iso _ (dx + r)) (family.iso _ dx) (i + j)
        (cup (space B.total) (cohomologyPullback (spaceMap B.projection) i a) b)) =
      cup (space X) a
        (cohomologyPushforward (P B.projection) (D B.total) (D X) (dx + r) dx
          (family.iso _ (dx + r)) (family.iso _ dx) j b)

end MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses
