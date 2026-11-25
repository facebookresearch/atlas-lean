/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Actual centered real valuations and section filtrations

The valuation is Mathlib's genuine multiplicative valuation of the actual
function field. Its center is tested on the actual stalk and maximal ideal;
the field-normalization fixes all nonzero base scalars. Section filtrations
are preimages of the actual valuation bound through a normalized section/germ
evaluation. They are proved submodules, not spans that conceal a failed bound.

Volume and expected/basis vanishing use those actual subspaces, dimensions,
and Lebesgue integrals. Geometric monomial retractions and their discrepancy
extension are requested separately. These formulas cover any field and any
line bundle; ordinary bigness/finite-section and model-normalization inputs
remain explicit. Source: Blum--Jonsson, arXiv1706.04548v2, Theorems A/C.
Native ring valuations and the completed Atlas log-pair/section producers
are reused, rather than replaced by valuation or volume scores.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CenteredValuationSections

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open scoped BigOperators ENNReal

variable {k : Type} [Field k] {n : ℕ}

/-- An actual real-valued valuation with its geometric stalk center, allowing the trivial value. -/
structure CenteredValuation (V : NormalVariety k n) where
  valuation : Valuation (FunctionField V) NNReal
  center : V.X.left
  scalars : ∀ a : k, a ≠ 0 → valuation (fractionScalar V a) = 1
  bounded : ∀ a : LocalRing V center, valuation (localToField V center a) ≤ 1
  strict : ∀ a : LocalRing V center, a ∈ IsLocalRing.maximalIdeal (LocalRing V center) →
    valuation (localToField V center a) < 1

/-- The actual logarithmic vanishing order of a nonzero rational function. -/
def order {V : NormalVariety k n} (v : CenteredValuation V) (a : (FunctionField V)ˣ) : ℝ :=
  -Real.log (v.valuation a : ℝ)

/-- A fixed normalized section evaluation yields the actual valuation-bound subspace. -/
def filteredSpace {V : NormalVariety k n} (v : CenteredValuation V) (M : V.X.left.Modules)
    (E : Evaluation V v.center M) (t : ℝ) : Submodule k (SectionSpace V M) := by
  letI := fractionAlgebra V
  have h0 : v.valuation (E.map 0) ≤ Real.toNNReal (Real.exp (-t)) := by
    rw [E.map.map_zero, Valuation.map_zero]
    exact zero_le
  exact
    { carrier := {s | v.valuation (E.map s) ≤ Real.toNNReal (Real.exp (-t))}
      zero_mem' := h0
      add_mem' := by
        intro a b ha hb
        change v.valuation (E.map (a + b)) ≤ _
        simpa only [map_add] using v.valuation.map_add_le ha hb
      smul_mem' := by
        intro a s hs
        by_cases h : a = 0
        · subst a
          change v.valuation (E.map ((0 : k) • s)) ≤ _
          rw [zero_smul]
          exact h0
        · change v.valuation (E.map (a • s)) ≤ _
          rw [E.map.map_smul]
          change v.valuation (algebraMap k (FunctionField V) a * E.map s) ≤ _
          rw [v.valuation.map_mul]
          have ha : v.valuation (algebraMap k (FunctionField V) a) = 1 := by
            exact v.scalars a h
          rw [ha, one_mul]
          exact hs }

/-- A line and its actual section/evaluation data in every tensor degree.
No graded section dimensions or evaluations are given as numerical functions. -/
structure SectionSeries (V : NormalVariety k n) (v : CenteredValuation V) where
  line : V.X.left.Modules
  isLine : IsLineBundle line
  evaluation : ∀ m : ℕ, Evaluation V v.center (power line m)
  finite : ∀ m : ℕ, Module.Finite k (SectionSpace V (power line m))

/-- The actual asymptotic section volume, retaining infinity. -/
def volume {V : NormalVariety k n} {v : CenteredValuation V} (S : SectionSeries V v) : ENNReal :=
  Filter.limsup
    (fun m : ℕ => (n.factorial : ENNReal) *
      (Module.finrank k (SectionSpace V (power S.line m)) : ENNReal) / (m : ENNReal)^n)
    Filter.atTop

/-- The filtered volume is the limsup of the actual filtered section dimensions. -/
def filteredVolume {V : NormalVariety k n} {v : CenteredValuation V} (S : SectionSeries V v)
    (t : ℝ) : ENNReal :=
  Filter.limsup
    (fun m : ℕ => (n.factorial : ENNReal) *
      (Module.finrank k (filteredSpace v (power S.line m) (S.evaluation m) ((m : ℝ)*t)) : ENNReal) /
      (m : ENNReal)^n) Filter.atTop

/-- Expected vanishing is the actual nonnegative volume integral divided by volume. -/
def expectedVanishing {V : NormalVariety k n} {v : CenteredValuation V} (S : SectionSeries V v) :
    ENNReal :=
  (∫⁻ t in Set.Ioi (0 : ℝ), filteredVolume S t) / volume S

/-- A finite-basis expected order, computed from actual rational section values.
Positive degree/nonzero basis images must be supplied at its use. -/
def basisExpectedOrder {V : NormalVariety k n} {v : CenteredValuation V}
    (S : SectionSeries V v) (m N : ℕ)
    (b : Module.Basis (Fin N) k (SectionSpace V (power S.line m))) : ℝ :=
  (∑ i, -Real.log (v.valuation ((S.evaluation m).map (b i)) : ℝ)) /
    ((m : ℝ) * N)

end MathlibExt.AlgebraicGeometry.CenteredValuationSections
