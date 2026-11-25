/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import MathlibExt.AlgebraicGeometry.BirationalResolution
public import MathlibExt.AlgebraicGeometry.BettiGysin
public import MathlibExt.AlgebraicGeometry.CartierIdealModels

/-!
# Blowup geometry and its actual Betti comparison map

The center is an actual closed scheme map. Its inverse ideal is effective
Cartier on the blowing-up scheme, and the factorization condition is the
actual blowup universal property. The exceptional scheme is the fiber
product with that center.

The exceptional degree-two class is minus pullback of its own Gysin unit; it
is the hyperplane class of the exceptional divisor for complex orientations.
All exceptional contributions use that class, actual Yoneda products and
the normalized derived pullback/proper maps. There is no chosen blowup
cohomology operator or supplied projective-bundle class.

Covered algebraic support: AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Blowup/ClassifyingMorphism.lean` and
`Blowup/ExceptionalProjectivizedNormalCone.lean`.
References: Stacks Tags 0806 and 01OF; Fulton, *Intersection Theory*,
Chapter 6 and Section 19.1. The actual Betti splitting is requested separately.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BlowupBettiModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves BettiRealization
open ProperBettiFunctoriality BettiFunctoriality BettiGysin
open BirationalResolution
open CartierIdealModels
open scoped BigOperators

attribute [local instance] HasDerivedCategory.standard

/-- A blowup of `X` along the closed subscheme `i : Z ⟶ X` (a closed
immersion), characterized by the universal property: the inverse image of the
ideal of `Z` is effective Cartier, and every morphism over `ℂ` with that
property factors uniquely. The source is integral and the map is proper and
birational. -/
structure BlowupModel {X Z : ComplexScheme} (i : Z ⟶ X) [IsClosedImmersion i.left] where
  /-- The blowing-up scheme. -/
  source : ComplexScheme
  /-- It is integral. -/
  [integral : IsIntegral source.left]
  /-- The blowing-down map. -/
  map : source ⟶ X
  /-- It is proper. -/
  [proper : IsProper map.left]
  /-- It is birational. -/
  birational : IsBirationalMorphism map.left
  /-- The inverse image of the ideal of the center is effective Cartier. -/
  cartier : IsEffectiveCartier (i.left.ker.comap map.left)
  /-- The universal property of the blowup. -/
  universal : ∀ (T : ComplexScheme) (f : T ⟶ X),
    IsEffectiveCartier (i.left.ker.comap f.left) →
      ∃! g : T ⟶ source, g ≫ map = f

namespace BlowupModel

variable {X Z : ComplexScheme} {i : Z ⟶ X} [IsClosedImmersion i.left] (B : BlowupModel i)

/-- The exceptional scheme: the fibre product of the blowup with the center. -/
abbrev exceptional : ComplexScheme :=
  Over.mk (pullback.fst B.map.left i.left ≫ B.source.hom)

/-- The inclusion of the exceptional scheme. -/
def exceptionalMap : B.exceptional ⟶ B.source :=
  Over.homMk (pullback.fst B.map.left i.left) (by rfl)

/-- The projection of the exceptional scheme to the center. -/
def exceptionalProjection : B.exceptional ⟶ Z :=
  Over.homMk (pullback.snd B.map.left i.left) (by
    dsimp [exceptional]
    rw [← i.w, ← Category.assoc, ← pullback.condition, Category.assoc, B.map.w])

instance : IsClosedImmersion B.exceptionalMap.left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst B.map.left i.left))

@[reassoc] theorem exceptional_square :
    B.exceptionalMap ≫ B.map = B.exceptionalProjection ≫ i := by
  apply Over.OverMorphism.ext
  exact pullback.condition

end BlowupModel

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X],
    MathlibExt.AlgebraicGeometry.CompactSupportBetti.DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))

variable {X Z : ComplexScheme} (i : Z ⟶ X) [IsClosedImmersion i.left]
  (B : BlowupModel i) (d c : ℕ) (hc : 2 ≤ c)
  [IsComplexVariety X] [IsComplexVariety Z] [IsComplexVariety B.source]
  [IsComplexVariety B.exceptional]
  [SmoothOfRelativeDimension (d + c) X.hom]
  [SmoothOfRelativeDimension d Z.hom]
  [SmoothOfRelativeDimension (d + c) B.source.hom]
  [SmoothOfRelativeDimension (d + c - 1) B.exceptional.hom]

/-- The Gysin map of the exceptional inclusion, which raises degrees by two. -/
def exceptionalPush (F : PureFamily D) (n : ℤ) :
    Cohomology (space B.exceptional) n →ₗ[ℚ]
      Cohomology (space B.source) (n + 2) :=
  cohomologyCast (by omega) ∘ₗ
    cohomologyPushforward (P B.exceptionalMap)
      (D B.exceptional) (D B.source) (d + c - 1) (d + c)
      (F.iso _ (d + c - 1)) (F.iso _ (d + c)) n

/-- The purity-dependent exceptional class `h ∈ H²(E)`: minus the restriction
to `E` of the Gysin image of `1`. For complex orientations it is
`c₁(O_E(1)) = -c₁(N_{E/B})`; other purity choices rescale it by a locally
constant unit. -/
def exceptionalClass (F : PureFamily D) : Cohomology (space B.exceptional) 2 :=
  -(cohomologyPullback (spaceMap B.exceptionalMap) 2
    (exceptionalPush D P i B d c hc F 0 (unitClass (space B.exceptional))))

/-- The `j`-th exceptional summand `Hⁿ⁻²⁽ʲ⁺¹⁾(Z) → Hⁿ(B)`,
`β ↦ i_{E!}(hʲ ∪ p^* β)`. -/
def exceptionalContribution (F : PureFamily D) (n : ℤ) (j : Fin (c - 1)) :
    Cohomology (space Z) (n - 2 * (j.val + 1)) →ₗ[ℚ]
      Cohomology (space B.source) n :=
  cohomologyCast (by omega) ∘ₗ
    exceptionalPush D P i B d c hc F (n - 2) ∘ₗ
      cohomologyCast (by omega) ∘ₗ
        cupRight (space B.exceptional)
          (powerClass (space B.exceptional) (exceptionalClass D P i B d c hc F) j.val) ∘ₗ
            cohomologyPullback (spaceMap B.exceptionalProjection)
              (n - 2 * (j.val + 1))

/-- The source of the blowup comparison: `Hⁿ(X) × ∏_{j < c - 1} Hⁿ⁻²⁽ʲ⁺¹⁾(Z)`. -/
abbrev BlowupSummands (n : ℤ) :=
  Cohomology (space X) n ×
    ((j : Fin (c - 1)) → Cohomology (space Z) (n - 2 * (j.val + 1)))

/-- The blowup comparison map `(α, β) ↦ π^* α + ∑ⱼ i_{E!}(hʲ ∪ p^* βⱼ)`. For
complex orientations this is the map of Voisin, Theorem 7.31; other purity
choices change the exceptional summands by invertible rescalings. -/
def blowupComparison (F : PureFamily D) (n : ℤ) :
    BlowupSummands (X := X) (Z := Z) c n →ₗ[ℚ] Cohomology (space B.source) n where
  toFun a := cohomologyPullback (spaceMap B.map) n a.1 +
    ∑ j, exceptionalContribution D P i B d c hc F n j (a.2 j)
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
    abel
  map_smul' r a := by
    simp only [Prod.smul_def, Pi.smul_apply, map_smul,
      Finset.smul_sum, smul_add, RingHom.id_apply]

end MathlibExt.AlgebraicGeometry.BlowupBettiModels
