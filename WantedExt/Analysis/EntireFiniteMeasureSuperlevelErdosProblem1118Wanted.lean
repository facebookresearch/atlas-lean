/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-measure superlevel sets of entire functions (Erdős Problem 1118)

Erdős Problem 1118: let `f` be a non-constant entire function such that, for some `c`, `E(c) = {z :
|f(z)| > c}` has finite measure. What is the minimum growth rate of `f`? If `E(c)` has finite
measure, must there exist `c' < c` such that `E(c')` has finite measure?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.EntireFiniteMeasureSuperlevelErdosProblem1118Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1118, https://www.erdosproblems.com/1118 (status
SOLVED). UnsolvedMath record UM-30007167 (`EP-1118`), dataset ulamai/UnsolvedMath v1.8.0.

Only the second question is formalized; the growth question (answered by Hayman's integral condition
`∫ r / log log M(r) dr < ∞`, proved by Camera and by Gol'dberg) is not. Measure is Lebesgue measure
on `ℂ`.
-/

/-- Erdős Problem 1118, second question: if `f` is a non-constant entire function and
`E(c) = {z : |f(z)| > c}` has finite measure, then `E(c')` has finite measure for some `c' < c`. -/
def finiteMeasureSuperlevelLowerable : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → (∃ z w, f z ≠ f w) → ∀ c : ℝ,
    MeasureTheory.volume {z : ℂ | c < ‖f z‖} < ⊤ →
      ∃ c' < c, MeasureTheory.volume {z : ℂ | c' < ‖f z‖} < ⊤

/--
Resolved false: Gol'dberg proved that for every `m > 0` some entire `f` has `{c > 0 : E(c) has
finite measure} = [m, ∞)`, so `E(m)` has finite measure while `E(c')` has infinite measure for every
`c' < m`; erdosproblems.com/1118 records the negative answer. Source: T. F. Bloom, Erdős Problems,
Problem #1118, https://www.erdosproblems.com/1118 (status SOLVED); resolution: A. A. Gol'dberg, Sets
on which the modulus of an entire function has a lower bound, Sibirsk. Mat. Zh. (1979), 512-518, for
any m > 0 there are entire f whose set T = {c > 0 : |E(c)| < ∞} is [m, ∞) (erdosproblems.com/1118),
https://www.erdosproblems.com/1118.
-/
public theorem_wanted finiteMeasureSuperlevelLowerable_refuted : ¬ finiteMeasureSuperlevelLowerable

end MathlibExt.Analysis.EntireFiniteMeasureSuperlevelErdosProblem1118Wanted
