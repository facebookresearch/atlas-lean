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
**Existence of the Cauchy principal value of $\varphi(x)/x$.** For every real-valued Schwartz
function $\varphi$ on $\mathbb{R}$ there is a real number $L$ such that
$\int_{\{x \in \mathbb{R} \,:\, |x| \ge \varepsilon\}} \varphi(x)/x \, dx \to L$ as
$\varepsilon \to 0^+$, the integrals being taken with respect to Lebesgue measure.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Distributions on R^d" / entry "Cauchy principal values";
F. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, Ch. 2.
-/
public theorem_wanted cauchyPrincipalValue_exists (φ : 𝓢(ℝ, ℝ)) :
    ∃ L : ℝ, Filter.Tendsto (fun ε : ℝ => ∫ x in {x : ℝ | ε ≤ |x|}, φ x / x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

end MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted
