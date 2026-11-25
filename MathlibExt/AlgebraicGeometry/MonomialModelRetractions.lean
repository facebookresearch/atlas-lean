/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CenteredValuationSections
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Geometric monomial charts and real-valuation retractions

A chart uses the actual regular local ring of a proper birational model,
its actual residue field, regular parameters and an injective coefficient
expansion into the actual power-series ring. The constant coefficient is
the residue map. Coefficient expansions are explicit source-integration
inputs (completion/Cohen structure), not newly requested completions.

The weighted norm is the supremum of actual supported monomial weights.
A geometric retraction is a genuine field valuation whose value on every
local function equals that formula. Charts contain the actual pulled
log-boundary support at the center. The extended discrepancy is the
supremum of the computed weighted divisorial discrepancies over these
actual charts and model lifts. No discrepancy function is supplied.

Source: Blum--Jonsson, arXiv1706.04548v2, §§3--5 and Theorems A/C;
Jonsson--Mustaţă, arXiv1011.3699, §3 (quasimonomial valuations).
Native valuations, regular local rings, coefficients and Atlas's
normalized canonical forms/divisorial discrepancies are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MonomialModelRetractions

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CenteredValuationSections
open scoped BigOperators

variable {k : Type} [Field k] {n : ℕ}

/-- A coefficient expansion of an actual regular local stalk. -/
structure CompletionChart (V : NormalVariety k n) (x : V.X.left) where
  [regular : IsRegularLocalRing (LocalRing V x)]
  dimension : ℕ
  dimension_eq : ringKrullDim (LocalRing V x) = (dimension : ℕ)
  parameters : Fin dimension → LocalRing V x
  maximal : Ideal.span (Set.range parameters) = IsLocalRing.maximalIdeal (LocalRing V x)
  expansion : LocalRing V x →+* MvPowerSeries (Fin dimension)
    (IsLocalRing.ResidueField (LocalRing V x))
  injective : Function.Injective expansion
  parameter_expansion : ∀ i, expansion (parameters i) = MvPowerSeries.X i
  residue : ∀ a, MvPowerSeries.constantCoeff (expansion a) =
    IsLocalRing.residue (LocalRing V x) a

/-- Supremum of the actual supported monomial norms; the empty support gives zero. -/
def monomialNorm {d : ℕ} {κ : Type} [Field κ] (w : Fin d → ℝ)
    (f : MvPowerSeries (Fin d) κ) : NNReal :=
  sSup {q | ∃ a : Fin d →₀ ℕ, MvPowerSeries.coeff a f ≠ 0 ∧
    q = ∏ i : Fin d, Real.toNNReal (Real.exp (-w i)) ^ a i}

/-- A field valuation normalized on every actual local function by the fixed expansion. -/
structure MonomialRetraction {V : NormalVariety k n} {x : V.X.left}
    (C : CompletionChart V x) (w : Fin C.dimension → ℝ) where
  valuation : CenteredValuation V
  center_eq : valuation.center = x
  normalized : ∀ a : LocalRing V x,
    valuation.valuation (localToField V x a) = monomialNorm w (C.expansion a)

/-- A lift of a centered valuation $v$ on the variety of the log pair $P$ to a proper birational
model $M$ of $P$: a centered valuation on the variety of $M$ that agrees with $v$ on rational
functions (through the function-field isomorphism of $M$) and whose center maps to the center of
$v$. -/
structure ModelLift {P : LogPair k n} (v : CenteredValuation P.variety)
    (M : BirationalModel P) where
  valuation : CenteredValuation M.variety
  center_map : M.map.left valuation.center = v.center
  field_normalized : ∀ a : FunctionField P.variety,
    valuation.valuation (M.data.fieldIso a) = v.valuation a

/-- A regular chart whose parameter divisors contain the actual pulled log-boundary support. -/
structure DiscrepancyChart {P : LogPair k n} (v : CenteredValuation P.variety) where
  model : BirationalModel P
  [smooth : Smooth model.variety.X.hom]
  lift : ModelLift v model
  chart : CompletionChart model.variety lift.valuation.center
  divisors : Fin chart.dimension → PrimePoint model.variety
  contains : ∀ i, lift.valuation.center ∈
    closure ({(divisors i).val} : Set model.variety.X.left)
  parameter_orders : ∀ i j,
    model.variety.X.left.ord
      (localToField model.variety lift.valuation.center (chart.parameters i))
      (divisors j).val = if i = j then 1 else 0
  boundary_support : ∀ q : PrimePoint model.variety,
    lift.valuation.center ∈ closure ({q.val} : Set model.variety.X.left) →
      pulledCombinationCoefficient model P.adjoint q -
        (canonicalDivisor model.data.canonical q : ℝ) ≠ 0 →
          ∃ i, divisors i = q

attribute [instance] DiscrepancyChart.smooth

/-- Weights are logarithms of the given valuation's actual parameter values. -/
def weights {P : LogPair k n} {v : CenteredValuation P.variety}
    (C : DiscrepancyChart v) (i : Fin C.chart.dimension) : ℝ :=
  -Real.log (C.lift.valuation.valuation
    (localToField C.model.variety C.lift.valuation.center (C.chart.parameters i)) : ℝ)

/-- The chart contribution uses the actual canonical/Cartier divisorial discrepancies. -/
def chartDiscrepancy {P : LogPair k n} {v : CenteredValuation P.variety}
    (C : DiscrepancyChart v) : ℝ :=
  ∑ i, weights C i * LogPairs.logDiscrepancy C.model (C.divisors i)

/-- The chart supremum of discrepancies: the supremum of the chart contributions over all
discrepancy charts of `v`. When `v` has no chart it is `⊥`, which is not a discrepancy (charts
need smooth birational models, which may not exist, e.g. over imperfect fields); use it as a
discrepancy only under `HasDiscrepancyCharts v`. -/
def extendedDiscrepancy {P : LogPair k n} (v : CenteredValuation P.variety) : EReal :=
  sSup {a | ∃ C : DiscrepancyChart v, a = (chartDiscrepancy C : EReal)}

/-- The valuation has a discrepancy chart, so that `extendedDiscrepancy v` is a supremum of
actual chart discrepancies. -/
def HasDiscrepancyCharts {P : LogPair k n} (v : CenteredValuation P.variety) : Prop :=
  Nonempty (DiscrepancyChart v)

/-- A concrete divisorial realization of a given valuation, fixing its scale and all values. -/
structure DivisorialRealization {P : LogPair k n} (v : CenteredValuation P.variety) where
  model : BirationalModel P
  prime : PrimePoint model.variety
  scale : ℝ
  positive : 0 < scale
  normalized : ∀ a : (FunctionField P.variety)ˣ,
    order v a = scale * (LogPairs.valuationOnBase model prime a : ℝ)

end MathlibExt.AlgebraicGeometry.MonomialModelRetractions
