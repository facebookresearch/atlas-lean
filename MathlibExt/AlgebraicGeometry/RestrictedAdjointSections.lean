/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps
public import MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
public import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Restricted adjoint sections and actual moving coefficients

An adjoint Cartier power is pinned coefficientwise to m(K+Delta).
Restriction is the native scheme/module pullback of its actual sections;
the restricted space is its literal linear image. The divisor on the
target can subsequently be identified by a normalized residue/different
comparison, but is not replaced here by a freely named adjoint.

Fixed/moving coefficients on any proper birational model are the minima
of the actual pulled-back section orders at its actual prime points.
The evaluator is a native local frame/germ map, not a moving-divisor score.
Degreewise tensor multiplication and birational/reflexive adjunction
comparisons remain explicit source-integration inputs on these carriers.

Source: Hacon--Xu, arXiv1302.0298v2, introduction and §2 (restricted
algebras and mobile b-divisors); BCHM, arXivmath/0610203v2, §3.6.
Native Cartier/module/field operations are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RestrictedAdjointSections

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

variable {k : Type} [Field k] {n d : ℕ}

/-- A literal Cartier log-adjoint power, allowing coefficient-one boundaries. -/
structure AdjointPower (P : LogPair k n) (m : ℕ) where
  cartier : CartierLine P.variety
  normalized : realCast cartier.divisor =
    (m : ℝ) • (realCast (canonicalDivisor P.canonical) + P.boundary)

/-- The actual restriction target and linearity comparison of its native section map. -/
structure Restriction {P : LogPair k n} {m : ℕ} (A : AdjointPower P m)
    (S : NormalVariety k d) (i : S.X ⟶ P.variety.X) where
  [closed : IsClosedImmersion i.left]
  linear : GenericSectionMaps.PullbackLinear i A.cartier.line.val
    ((Scheme.Modules.pullback i.left).obj A.cartier.line.val)
    (𝟙 ((Scheme.Modules.pullback i.left).obj A.cartier.line.val))

/-- Literal linear image of the actual H0 restriction. -/
def restrictedSpace {P : LogPair k n} {m : ℕ} {A : AdjointPower P m}
    {S : NormalVariety k d} {i : S.X ⟶ P.variety.X} (R : Restriction A S i) :=
  LinearMap.range R.linear.map

/-- Pullback of the same adjoint sections to an actual birational model,
with its evaluation characterized at every actual prime point. The pulled
complete linear series is nonempty, so that its fixed and moving parts are
defined; an empty series has no fixed divisor. -/
structure ModelSections {P : LogPair k n} {m : ℕ} (A : AdjointPower P m)
    (M : BirationalModel P) where
  linear : GenericSectionMaps.PullbackLinear M.map A.cartier.line.val
    ((Scheme.Modules.pullback M.map.left).obj A.cartier.line.val)
    (𝟙 ((Scheme.Modules.pullback M.map.left).obj A.cartier.line.val))
  nonempty : ∃ s, linear.map s ≠ 0
  evaluations : ∀ p : PrimePoint M.variety,
    Evaluation M.variety p.val ((Scheme.Modules.pullback M.map.left).obj A.cartier.line.val)

/-- Actual fixed coefficient of a pulled complete linear series: the least order
at `p` of a nonzero pulled section. The set is nonempty (`ModelSections.nonempty`)
and bounded below by zero (pulled sections are regular at `p`), so this infimum
is attained. -/
def fixedCoefficient {P : LogPair k n} {m : ℕ} {A : AdjointPower P m}
    {M : BirationalModel P} (S : ModelSections A M) (p : PrimePoint M.variety) : ℤ :=
  sInf {a | ∃ s : GenericSectionMaps.Sections P.variety.X A.cartier.line.val,
    S.linear.map s ≠ 0 ∧
      a = M.variety.X.left.ord ((S.evaluations p).map (S.linear.map s)) p.val}

/-- The actual image whose base ideal determines the fixed part. -/
def modelSectionSpace {P : LogPair k n} {m : ℕ} {A : AdjointPower P m}
    {M : BirationalModel P} (S : ModelSections A M) :=
  LinearMap.range S.linear.map

/-- Actual mobile-divisor coefficient, retaining the source Cartier divisor choice. -/
def movingCoefficient {P : LogPair k n} {m : ℕ} {A : AdjointPower P m}
    {M : BirationalModel P} (S : ModelSections A M) (p : PrimePoint M.variety) : ℤ :=
  pulledCartierCoefficient M A.cartier p - fixedCoefficient S p

/-- An actual proper birational refinement, with the function-field map fixed by its generic map. -/
structure ModelRefinement {P : LogPair k n} (M₁ M₂ : BirationalModel P) where
  map : M₂.variety.X ⟶ M₁.variety.X
  [proper : IsProper map.left]
  over : map ≫ M₁.map = M₂.map
  generic : map.left (genericPoint M₂.variety.X.left) = genericPoint M₁.variety.X.left
  fieldIso :
    letI := fractionAlgebra M₁.variety
    letI := fractionAlgebra M₂.variety
    FunctionField M₁.variety ≃ₐ[k] FunctionField M₂.variety
  normalized : fieldIso.toRingHom = (genericMap map generic).hom

/-- A fixed part represented by an actual Cartier line, pinned to the actual minimum orders. -/
structure FixedCartierPart {P : LogPair k n} {m : ℕ} {A : AdjointPower P m}
    {M : BirationalModel P} (S : ModelSections A M) where
  cartier : CartierLine M.variety
  normalized : ∀ p, cartier.divisor p = fixedCoefficient S p

/-- Pullback of the actual fixed Cartier part on a refined model. -/
def pulledFixedCoefficient {P : LogPair k n} {m : ℕ} {A : AdjointPower P m}
    {M₁ M₂ : BirationalModel P} {S : ModelSections A M₁}
    (R : ModelRefinement M₁ M₂) (F : FixedCartierPart S) (p : PrimePoint M₂.variety) : ℤ :=
  M₂.variety.X.left.ord
    (R.fieldIso (F.cartier.functions
      (Classical.choose (F.cartier.covers (R.map.left p.val))))) p.val

/-- Native local powers of a section, using the actual presheaf tensor/sheafification maps. -/
def localPowerSection {X : Scheme.{0}} (L : X.Modules) (U : X.Opens) (s : Γ(L,U)) :
    (m : ℕ) → Γ(LineBundleTaskContracts.power L m,U)
  | 0 => (1 : Γ(X,U))
  | m+1 => NormalizedModuleTensorMaps.pureTensorSection X
      (LineBundleTaskContracts.power L m) L U (localPowerSection L U s m) s

/-- Actual power multiplication, fixed on every local line generator;
no free graded-ring carrier. -/
structure SectionProduct {X : Scheme.{0}} (L : X.Modules) where
  line : IsLineBundle L
  map : ∀ a b,
    AlgebraicLineBundleFamilies.moduleTensor X (LineBundleTaskContracts.power L a)
      (LineBundleTaskContracts.power L b) ⟶ LineBundleTaskContracts.power L (a+b)
  normalized : ∀ (U : X.Opens) (s : Γ(L,U)) a b,
    (map a b).app U (NormalizedModuleTensorMaps.pureTensorSection X
      (LineBundleTaskContracts.power L a) (LineBundleTaskContracts.power L b) U
        (localPowerSection L U s a) (localPowerSection L U s b)) =
      localPowerSection L U s (a+b)

/-- Complete section multiplication computed from the native unit/tensor maps
and fixed local product. -/
def sectionProduct {X : _root_.CategoryTheory.Over (Spec (.of k))} {L : X.left.Modules}
    (P : SectionProduct L) (a b : ℕ)
    (s : GenericSectionMaps.Sections X (LineBundleTaskContracts.power L a))
    (t : GenericSectionMaps.Sections X (LineBundleTaskContracts.power L b)) :
    GenericSectionMaps.Sections X (LineBundleTaskContracts.power L (a+b)) :=
  GenericSectionMaps.homSection X
    (LineBundleTaskContracts.tensorSection
      (GenericSectionMaps.sectionHom X _ s) (GenericSectionMaps.sectionHom X _ t) ≫ P.map a b)

/-- Local normalization of the fixed native power/pullback comparison on every section. -/
structure LocalPowerPullback {X Y : _root_.CategoryTheory.Over (Spec (.of k))}
    (f : Y ⟶ X) (L : X.left.Modules) (P : LineBundleTaskContracts.PullbackPowers f.left) where
  normalized : ∀ (U : X.left.Opens) (W : Y.left.Opens) (h : W ≤ f.left ⁻¹ᵁ U)
    (s : Γ(L,U)) m,
    ((P.comparison m).hom.app L).app W
      (GenericSectionMaps.localPullbackSection f.left (LineBundleTaskContracts.power L m) U W h
        (localPowerSection L U s m)) =
    localPowerSection ((Scheme.Modules.pullback f.left).obj L) W
      (GenericSectionMaps.localPullbackSection f.left L U W h s) m

/-- Actual degreewise restriction map on the same native line powers. -/
structure PowerRestriction {X Y : _root_.CategoryTheory.Over (Spec (.of k))}
    (f : Y ⟶ X) (L : X.left.Modules) (P : LineBundleTaskContracts.PullbackPowers f.left) where
  linear : ∀ m, GenericSectionMaps.PullbackLinear f (LineBundleTaskContracts.power L m)
    (LineBundleTaskContracts.power ((Scheme.Modules.pullback f.left).obj L) m)
      ((P.comparison m).hom.app L)

/-- The proposition that restriction of sections of tensor powers is multiplicative: for a morphism
$f : Y \to X$ of $k$-schemes, a line bundle $L$ on $X$ with section products `A` (`SectionProduct`:
maps $L^{\otimes a} \otimes L^{\otimes b} \to L^{\otimes (a + b)}$ normalized on local powers),
section products `B` on $f^*L$, comparisons $f^*(L^{\otimes m}) \cong (f^*L)^{\otimes m}$ (`P`) and
the restriction maps $R_m : H^0(X, L^{\otimes m}) \to H^0(Y, (f^*L)^{\otimes m})$ given by pullback
followed by the comparison (`PowerRestriction`), $R_{a+b}(s \cdot t) = R_a(s) \cdot R_b(t)$ for all
$a, b$ and all global sections $s$ of $L^{\otimes a}$ and $t$ of $L^{\otimes b}$, the products
being those of `A` and `B`. -/
structure RestrictionAlgebra {X Y : _root_.CategoryTheory.Over (Spec (.of k))}
    (f : Y ⟶ X) (L : X.left.Modules) (P : LineBundleTaskContracts.PullbackPowers f.left)
    (A : SectionProduct L) (B : SectionProduct ((Scheme.Modules.pullback f.left).obj L))
    (R : PowerRestriction f L P) : Prop where
  multiplicative : ∀ a b
    (s : GenericSectionMaps.Sections X (LineBundleTaskContracts.power L a))
    (t : GenericSectionMaps.Sections X (LineBundleTaskContracts.power L b)),
    (R.linear (a+b)).map (sectionProduct A a b s t) =
      sectionProduct B a b ((R.linear a).map s) ((R.linear b).map t)

end MathlibExt.AlgebraicGeometry.RestrictedAdjointSections
