/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory
open scoped SchwartzMap

namespace MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted

/--
The Cauchy principal value of `φ(x)/x` exists for Schwartz `φ`: the symmetric-exclusion
integrals converge as the exclusion radius tends to `0`.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Distributions on R^d" / entry "Cauchy principal values";
F. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, Ch. 2.
-/
public theorem_wanted cauchyPrincipalValue_exists (φ : 𝓢(ℝ, ℝ)) :
    ∃ L : ℝ, Filter.Tendsto (fun ε : ℝ => ∫ x in {x : ℝ | ε ≤ |x|}, φ x / x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

end MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted
