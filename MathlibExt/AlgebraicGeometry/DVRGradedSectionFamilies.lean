/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DVRSectionLattices
public import MathlibExt.AlgebraicGeometry.RestrictedAdjointSections
public import MathlibExt.AlgebraicGeometry.ConductorLogGluing
public import MathlibExt.AlgebraicGeometry.MonomialModelRetractions
public import MathlibExt.AlgebraicGeometry.RelativeMoriContracts

/-!
# Fixed two-model graded DVR section lattices

Both model schemes and both lines are fixed in every degree. The common
generic identification is a single actual scheme isomorphism together with a
chosen line comparison `lineIso`. All higher-degree comparisons are computed
from these by native pullback power maps and are fixed on every local line
generator.

The filtrations here are *raw* lattice filtrations attached to the chosen line
comparison: `forwardFiltration C u m a` is the reduction of the first lattice
intersected with `π^a` times the second. They are not Blum--Xu's indexed
filtrations. Even for the comparison induced by the isomorphism of the generic
log pairs (which is not encoded here; `LogAnticanonicalModels` does not
determine `lineIso`), Blum--Xu's filtration in degree `m` is a reindexing of the
raw one by a discrepancy shift: in arXiv1812.03538v2, §§5.1.1--5.1.2 their map
carries the factor `t^(m r a − p)`, with `a` from their (11), so their step `p`
is the raw step `p − m r a` (and the reverse filtration uses `a'`). For
example, for two models `ℙ¹_R` without boundary glued by `y = t x`, the
anticanonical comparison sends `∂y, y ∂y, y² ∂y` to `t⁻¹ ∂x, x ∂x, t x² ∂x`, and
the raw `F⁰` has dimension `2` while Blum--Xu's `F⁰` is everything (dimension
`3`). Another choice of line comparison differs by an automorphism of the first
generic line, and the degree-`m` comparison then changes by its `m`-th power
(`powerIso_withLineAut`): for multiplication by `c ∈ Kˣ` the degree-`m` raw
filtration is shifted by `m · v(c)`. Such linear shifts do not change the
Rees-algebra statements requested downstream: the substitution
`z ↦ T^(-v(c)) z` fixes `T` and the section grading and identifies the two Rees
algebras, their coefficient descriptions and their relative `Proj`.

The forward and reverse specialization filtrations are the actual
DVR lattice intersection/rescaling/reduction operations. A relative
log-anticanonical adapter ties these lines to the actual proper
canonical/reflexive Hom-of-boundary-ideal power, not a free graded ring.
Sources: Blum--Xu arXiv1812.03538v2, §§2--3 and §5.1 (indexing).
Generic section/base-change/tensor/power facts remain source integration.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DVRSectionLattices
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.RestrictedAdjointSections
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences

/-- Comparison isomorphisms $f^*(L^{\otimes m}) \cong (f^*L)^{\otimes m}$ between pullback along a
morphism of schemes $f : Y \to X$ and tensor powers of sheaves of modules (`PullbackPowers f`),
normalized on local sections: for every sheaf of modules $L$ on $X$, opens $U \subseteq X$ and
$W \subseteq f^{-1}(U)$, section $s$ of $L$ over $U$ and $m \in \mathbb{N}$, the comparison sends
the pullback to $W$ of $s^{\otimes m}$ to the $m$-th tensor power of the pullback of $s$ to $W$
(with $s^{\otimes 0} = 1$). -/
structure PowerPullback {X Y : Scheme.{0}} (f : Y ⟶ X) where
  powers : PullbackPowers f
  normalized : ∀ (L : X.Modules) (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (s : Γ(L,U)) (m : ℕ),
    (((powers.comparison m).hom.app L).app W)
      (localPullbackSection f (power L m) U W h (localPowerSection L U s m)) =
    localPowerSection ((Scheme.Modules.pullback f).obj L) W
      (localPullbackSection f L U W h s) m

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Actual fixed models, one generic scheme isomorphism and one chosen generic line comparison,
with no per-degree model choice. The filtrations below are relative to `lineIso` (see the module
docstring for how they depend on it). -/
structure TwoModels where
  first : Over (Spec (.of R))
  firstLine : first.left.Modules
  firstLineBundle : IsLineBundle firstLine
  second : Over (Spec (.of R))
  secondLine : second.left.Modules
  secondLineBundle : IsLineBundle secondLine
  firstBase : ∀ m, SectionBaseChange (K := K) first (power firstLine m)
  secondBase : ∀ m, SectionBaseChange (K := K) second (power secondLine m)
  firstSpecial : ∀ m, SpecialSectionMap first (power firstLine m)
  secondSpecial : ∀ m, SpecialSectionMap second (power secondLine m)
  firstInjective : ∀ m, Function.Injective (genericSectionMap (firstBase m))
  secondInjective : ∀ m, Function.Injective (genericSectionMap (secondBase m))
  genericIso : genericFiber (K := K) first ≅ genericFiber (K := K) second
  lineIso : (Scheme.Modules.pullback genericIso.hom.left).obj
    (genericModule (K := K) second secondLine) ≅ genericModule (K := K) first firstLine
  firstPowers : PowerPullback (genericProjection (K := K) first)
  secondPowers : PowerPullback (genericProjection (K := K) second)
  genericPowers : PowerPullback genericIso.hom.left
  reversePowers : PowerPullback genericIso.inv.left

namespace TwoModels
variable (D : TwoModels (R := R) (K := K))

/-- Every forward module comparison is the power of the same chosen line comparison. -/
def powerIso (m : ℕ) :
    (Scheme.Modules.pullback D.genericIso.hom.left).obj
      (genericModule (K := K) D.second (power D.secondLine m)) ≅
        genericModule (K := K) D.first (power D.firstLine m) :=
  (Scheme.Modules.pullback D.genericIso.hom.left).mapIso
    ((D.secondPowers.powers.comparison m).app D.secondLine) ≪≫
  (D.genericPowers.powers.comparison m).app (genericModule (K := K) D.second D.secondLine) ≪≫
  (powerFunctor (genericFiber (K := K) D.first).left m).mapIso D.lineIso ≪≫
  ((D.firstPowers.powers.comparison m).app D.firstLine).symm

/-- The same models with the generic line comparison followed by an automorphism `e` of the
first generic line (for instance multiplication by a unit of the generic fibre). -/
def withLineAut
    (e : genericModule (K := K) D.first D.firstLine ≅ genericModule (K := K) D.first D.firstLine) :
    TwoModels (R := R) (K := K) :=
  { D with lineIso := D.lineIso ≪≫ e }

/-- Changing the line comparison by an automorphism `e` changes the degree-`m` comparison by the
`m`-th power of `e`, transported through the power comparison. -/
theorem powerIso_withLineAut
    (e : genericModule (K := K) D.first D.firstLine ≅ genericModule (K := K) D.first D.firstLine)
    (m : ℕ) :
    (D.withLineAut e).powerIso m = D.powerIso m ≪≫
      (D.firstPowers.powers.comparison m).app D.firstLine ≪≫
      (powerFunctor (genericFiber (K := K) D.first).left m).mapIso e ≪≫
      ((D.firstPowers.powers.comparison m).app D.firstLine).symm := by
  ext1
  simp [powerIso, withLineAut]

/-- The inverse line comparison is computed from the original isomorphism and native pasting. -/
def reverseLineIso :
    (Scheme.Modules.pullback D.genericIso.inv.left).obj
      (genericModule (K := K) D.first D.firstLine) ≅
        genericModule (K := K) D.second D.secondLine :=
  (Scheme.Modules.pullback D.genericIso.inv.left).mapIso D.lineIso.symm ≪≫
  (Scheme.Modules.pullbackComp D.genericIso.inv.left D.genericIso.hom.left).app
    (genericModule (K := K) D.second D.secondLine) ≪≫
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left D.genericIso.inv_hom_id)).app
    (genericModule (K := K) D.second D.secondLine) ≪≫
  (Scheme.Modules.pullbackId (genericFiber (K := K) D.second).left).app
    (genericModule (K := K) D.second D.secondLine)

def reversePowerIso (m : ℕ) :
    (Scheme.Modules.pullback D.genericIso.inv.left).obj
      (genericModule (K := K) D.first (power D.firstLine m)) ≅
        genericModule (K := K) D.second (power D.secondLine m) :=
  (Scheme.Modules.pullback D.genericIso.inv.left).mapIso
    ((D.firstPowers.powers.comparison m).app D.firstLine) ≪≫
  (D.reversePowers.powers.comparison m).app (genericModule (K := K) D.first D.firstLine) ≪≫
  (powerFunctor (genericFiber (K := K) D.second).left m).mapIso D.reverseLineIso ≪≫
  ((D.secondPowers.powers.comparison m).app D.secondLine).symm

/-- Proof-only linearity of the fixed actual higher-degree generic maps. -/
structure GradedComparisons where
  forward : ∀ m, PullbackLinear D.genericIso.hom
    (genericModule (K := K) D.second (power D.secondLine m))
    (genericModule (K := K) D.first (power D.firstLine m)) (D.powerIso m).hom
  reverse : ∀ m, PullbackLinear D.genericIso.inv
    (genericModule (K := K) D.first (power D.firstLine m))
    (genericModule (K := K) D.second (power D.secondLine m)) (D.reversePowerIso m).hom

def forwardModel (C : D.GradedComparisons) (m : ℕ) :
    ModelComparison (K := K) D.first (power D.firstLine m) where
  model := D.second
  module := power D.secondLine m
  baseChange := D.secondBase m
  genericIso := D.genericIso
  moduleIso := D.powerIso m
  sectionComparison := C.forward m

def reverseModel (C : D.GradedComparisons) (m : ℕ) :
    ModelComparison (K := K) D.second (power D.secondLine m) where
  model := D.first
  module := power D.firstLine m
  baseChange := D.firstBase m
  genericIso := D.genericIso.symm
  moduleIso := D.reversePowerIso m
  sectionComparison := C.reverse m

/-- The raw forward filtration in degree `m`: reductions of the first lattice intersected with
`π^a` times the second lattice (through `powerIso`). Blum--Xu's indexing differs by a discrepancy
shift (module docstring). -/
def forwardFiltration (C : D.GradedComparisons) (u : Uniformizer (R := R) (K := K))
    (m : ℕ) (a : ℤ) :=
  modelSpecializationFiltration (D.firstBase m) (D.firstInjective m) (D.firstSpecial m) u
    (D.forwardModel C m) a

/-- The raw reverse filtration in degree `m`, with the roles of the two models exchanged. -/
def reverseFiltration (C : D.GradedComparisons) (u : Uniformizer (R := R) (K := K))
    (m : ℕ) (a : ℤ) :=
  modelSpecializationFiltration (D.secondBase m) (D.secondInjective m) (D.secondSpecial m) u
    (D.reverseModel C m) a

end TwoModels

variable [HasDerivedPushforwards.{0}]

/-- Actual relative log-anticanonical lines and exact generic-boundary identification. These
make both lines relative log-anticanonical; they do not determine the generic line comparison
`D.lineIso`; the pair-induced comparison is not encoded, and even for it Blum--Xu's indices
differ from the raw ones by a discrepancy shift (see the module docstring). -/
structure LogAnticanonicalModels (D : TwoModels (R := R) (K := K)) (n : ℕ) where
  firstReference : ProperReference D.first.hom
  secondReference : ProperReference D.second.hom
  firstBoundary : D.first.left.IdealSheafData
  secondBoundary : D.second.left.IdealSheafData
  exponent : ℕ
  positive : 0 < exponent
  firstNormalized : D.firstLine =
    dual (ConductorLogGluing.logPower firstReference firstBoundary n exponent)
  secondNormalized : D.secondLine =
    dual (ConductorLogGluing.logPower secondReference secondBoundary n exponent)
  genericBoundary :
    firstBoundary.comap (genericProjection (K := K) D.first) =
      (secondBoundary.comap (genericProjection (K := K) D.second)).comap D.genericIso.hom.left


/-- A genuine polarized log-Fano fibre of an actual DVR model: a proper (`proper`) klt log pair
whose anticanonical class is ample, as for the geometric fibres of Blum--Xu's flat proper
families. Its boundary coefficients come from the actual ideal I_(eB), whose restriction to the
integral
special fibre is nonzero (`boundaryRestricts`: the boundary has a restriction to the fibre, so
e.g. the ideal of the special fibre itself is excluded), and its line comparison uses the fixed
relative log-anticanonical line. -/
structure LogFanoFibre (X : Over (Spec (.of R))) (L : X.left.Modules)
    (I : X.left.IdealSheafData) (n e : ℕ) where
  positive : 0 < e
  pair : LogPairs.LogPair (IsLocalRing.ResidueField R) n
  [proper : IsProper pair.variety.X.hom]
  calculus : LogPairs.HasModelCalculus pair
  klt : LogPairs.IsKlt pair
  schemeIso : specialFiber X ≅ pair.variety.X
  adjoint : AdjointPower pair e
  lineIso : (Scheme.Modules.pullback (schemeIso.inv.left ≫ specialProjection X)).obj L ≅
    dual adjoint.cartier.line.val
  boundaryRestricts : I.comap (schemeIso.inv.left ≫ specialProjection X) ≠ ⊥
  boundaryNormalized : ∀ p : LogPairs.PrimePoint pair.variety,
    (ConductorLogGluing.idealOrder pair.variety
      (I.comap (schemeIso.inv.left ≫ specialProjection X)) p : ℝ) = (e : ℝ) * pair.boundary p
  ample : RelativeMoriContracts.IsRelativelyAmpleR
    (CategoryTheory.Over.homMk pair.variety.X.hom :
      pair.variety.X ⟶ CategoryTheory.Over.mk (𝟙 (Spec (.of (IsLocalRing.ResidueField R)))))
    (RelativeMoriContracts.negativeCombination pair.adjoint)
  sectionSeries : ∀ v : CenteredValuationSections.CenteredValuation pair.variety,
    CenteredValuationSections.SectionSeries pair.variety v
  sectionLine : ∀ v, (sectionSeries v).line = dual adjoint.cartier.line.val

attribute [instance] LogFanoFibre.proper

/-- Valuative semistability of the log-Fano fibre (the Fujita--Li valuative criterion
`β(E) = A(E) − S(E) ≥ 0` for every prime divisor `E` over the fibre): at every divisorial valuation,
given by a divisor `R.prime` on a birational model with scale `R.scale`, the normalized expected
vanishing order `S` is at most the log discrepancy `R.scale · A(R.prime)`. Divisorial valuations
suffice for valuative semistability (Fujita; Li; as used by Blum--Xu). The log discrepancy is
the intrinsic one of the divisor, so no chart or monomialization hypothesis is involved and no
divisor is excluded for lack of charts. No stability score or nonarchimedean functional is
supplied. -/
def LogFanoFibre.IsValuativelySemistable
    {X : Over (Spec (.of R))} {L : X.left.Modules} {I : X.left.IdealSheafData}
    {n e : ℕ} (F : LogFanoFibre X L I n e) : Prop :=
  ∀ (v : CenteredValuationSections.CenteredValuation F.pair.variety)
    (D : MonomialModelRetractions.DivisorialRealization (P := F.pair) v),
    ((CenteredValuationSections.expectedVanishing (F.sectionSeries v)) : EReal) / (e : EReal) ≤
      ((D.scale * LogPairs.logDiscrepancy D.model D.prime : ℝ) : EReal)

/-- Valuatively semistable log-Fano special fibres for both models: log-Fano fibre structures on
the special fibres of the first and of the second model, with their given lines and with the
boundary ideals and exponent given by `B`, both valuatively semistable
(`LogFanoFibre.IsValuativelySemistable`). -/
structure SemistableSpecialFibres (D : TwoModels (R := R) (K := K)) {n : ℕ}
    (B : LogAnticanonicalModels D n) where
  first : LogFanoFibre D.first D.firstLine B.firstBoundary n B.exponent
  second : LogFanoFibre D.second D.secondLine B.secondBoundary n B.exponent
  firstSemistable : first.IsValuativelySemistable
  secondSemistable : second.IsValuativelySemistable

end MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies
