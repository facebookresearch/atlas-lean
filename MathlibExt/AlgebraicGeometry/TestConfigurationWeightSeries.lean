/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantSectionWeights
public import MathlibExt.AlgebraicGeometry.RestrictedAdjointSections
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Normalized central-fibre section weights of an actual test configuration

The central action is pinned by its actual closed-fibre inclusion. Its
line comparison is computed from the original line linearization and
native pullbackComp. Every power comparison and H0 coaction refers to
those fixed data. The finite weight spaces are actual coaction kernels.

The measure uses the antipode sign that converts pullback coaction
characters to the geometric action on sections. A test configuration's
scheme and generic line trivializations are also normalized by its
actual action on the identified fibre over one.

Generic equivariant pullback/power/decomposition proofs remain completed
source integration inputs. The asymptotic probability-measure comparison
is the remaining geometric Wanted result.
Source: Boucksom--Hisamoto--Jonsson arXiv1504.06568v3, Theorem A and §§2--3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
open MathlibExt.AlgebraicGeometry.LinearizedLineBundles
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.EquivariantSectionWeights
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

variable {k : Type} [Field k] {X : Over (Base k)} {L : X.left.Modules}

abbrev central (T : TestConfiguration k X L) := pullback T.projection (affinePoint k 0)
abbrev centralInclusion (T : TestConfiguration k X L) : central T ⟶ T.total :=
  pullback.fst T.projection (affinePoint k 0)

abbrev centralLine (T : TestConfiguration k X L) :=
  (Scheme.Modules.pullback (centralInclusion T).left).obj T.polarization

/-- The canonical central line map after a genuine invariant-fibre action is supplied. -/
def centralComparison (T : TestConfiguration k X L) [ModObj (Torus k) (central T)]
    (h : γ[Torus k,central T] ≫ centralInclusion T =
      (Torus k ◁ centralInclusion T) ≫ γ[Torus k,T.total]) :
    (Scheme.Modules.pullback (action (Torus k) (central T))).obj (centralLine T) ⟶
      (Scheme.Modules.pullback (projection (Torus k) (central T))).obj (centralLine T) :=
  (Scheme.Modules.pullbackComp (action (Torus k) (central T))
    (centralInclusion T).left).hom.app T.polarization ≫
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).hom.app T.polarization ≫
  reindexHom (Torus k ◁ centralInclusion T).left T.linearization.comparison.hom ≫
  (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left (whiskerLeft_snd (Torus k) (centralInclusion T)))).hom.app
      T.polarization ≫
  (Scheme.Modules.pullbackComp (projection (Torus k) (central T))
    (centralInclusion T).left).inv.app T.polarization

/-- A $\mathbb{G}_m$-linearization of the central fibre of a test configuration $T$ of $(X, L)$ over
a field $k$, induced from $T$: a $\mathbb{G}_m$-action on the central fibre $T_0$ (the fibre of $T$
over $0 \in \mathbb{A}^1$) for which the inclusion $T_0 \to T$ is equivariant, and a
$\mathbb{G}_m$-linearization of the restriction $L_0$ of the polarization of $T$ to $T_0$ whose
comparison isomorphism $a^*L_0 \cong \mathrm{pr}^*L_0$ is the one induced by the linearization of
$T$ along the inclusion (`centralComparison`). -/
structure CentralLinearization (T : TestConfiguration k X L) where
  [action : ModObj (Torus k) (central T)]
  over : γ[Torus k,central T] ≫ centralInclusion T =
    (Torus k ◁ centralInclusion T) ≫ γ[Torus k,T.total]
  linearization : Linearization (Torus k) (central T) (centralLine T)
  normalized : linearization.comparison.hom = centralComparison T over

/-- Proper ample polarization inputs on the actual generic and central fibres. -/
structure AmpleData (T : TestConfiguration k X L) where
  [baseNoetherian : IsNoetherian X.left]
  baseLine : ProjectiveLineSystems.LineBundle X.left
  baseNormalized : baseLine.val = L
  baseAmple : ProjectiveLineSystems.IsAmpleLine baseLine
  [fibreNoetherian : IsNoetherian (central T).left]
  fibreLine : ProjectiveLineSystems.LineBundle (central T).left
  fibreNormalized : fibreLine.val = centralLine T
  fibreAmple : ProjectiveLineSystems.IsAmpleLine fibreLine

/-- Actual finite-dimensional central-fibre section representations in every tensor degree. -/
structure WeightSeries (T : NormalizedTestConfiguration k X L) where
  centralData : CentralLinearization T.toTestConfiguration
  powerAction :
    letI := centralData.action
    PullbackPowers (action (Torus k) (central T.toTestConfiguration))
  powerProjection :
    letI := centralData.action
    PullbackPowers (projection (Torus k) (central T.toTestConfiguration))
  localAction :
    letI := centralData.action
    RestrictedAdjointSections.LocalPowerPullback
      γ[Torus k,central T.toTestConfiguration] (centralLine T.toTestConfiguration) powerAction
  localProjection :
    letI := centralData.action
    RestrictedAdjointSections.LocalPowerPullback
      (snd (Torus k) (central T.toTestConfiguration)) (centralLine T.toTestConfiguration)
        powerProjection
  linearization :
    letI := centralData.action
    ∀ m, Linearization (Torus k) (central T.toTestConfiguration)
      (power (centralLine T.toTestConfiguration) m)
  powerNormalized :
    letI := centralData.action
    ∀ m, (linearization m).comparison =
      powerComparison (Torus k) (central T.toTestConfiguration) centralData.linearization
        powerAction powerProjection m
  tensorSections :
    letI := centralData.action
    ∀ m, TensorSections (central T.toTestConfiguration)
      (power (centralLine T.toTestConfiguration) m)
  coaction :
    letI := centralData.action
    ∀ m, SectionCoaction (central T.toTestConfiguration)
      (power (centralLine T.toTestConfiguration) m) (linearization m) (tensorSections m)
  finiteWeights :
    letI := centralData.action
    ∀ m, FiniteWeights (coaction m)

/-- Geometric section-action measure, with the actual torus antipode applied to coaction weights.
It is normalized relative to the declared polarization `L`: the polarization of the test
configuration restricts to `L^r` (`r = exponent`) on the general fibre, so the weights of the
degree-`m` sections are divided by `r · m` (BHJ's Duistermaat--Heckman normalization). -/
def sectionMeasure {T : NormalizedTestConfiguration k X L} (S : WeightSeries T) (m : ℕ) :
    MeasureTheory.Measure ℝ := by
  letI := S.centralData.action
  exact MeasureTheory.Measure.map (fun x : ℝ => -x)
    (weightMeasure (S.finiteWeights m) (T.toTestConfiguration.exponent * m))

theorem sectionMeasure_eq {T : NormalizedTestConfiguration k X L} (S : WeightSeries T) (m : ℕ) :
    letI := S.centralData.action
    sectionMeasure S m = MeasureTheory.Measure.map (fun x : ℝ => -x)
      (weightMeasure (S.finiteWeights m) (T.toTestConfiguration.exponent * m)) :=
  rfl

/-- Weak convergence against every actual bounded continuous test function. -/
def HasWeakLimit {T : NormalizedTestConfiguration k X L} (S : WeightSeries T)
    (measure : MeasureTheory.Measure ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Filter.Tendsto (fun m : ℕ => ∫ x, f x ∂sectionMeasure S m) Filter.atTop
      (nhds (∫ x, f x ∂measure))

end MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries
