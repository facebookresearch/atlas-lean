/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

open MeasureTheory
open scoped SchwartzMap BigOperators

namespace MathlibExt.Analysis.Distribution.TemperedExamplesWanted

/--
The Dirac comb is a tempered distribution: summation over the integers extends to
`T : 𝓢'(ℝ, ℂ)` with `T g = ∑' n : ℤ, g n` on Schwartz functions.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Tempered distributions" / entry "Dirac comb";
<https://en.wikipedia.org/wiki/Dirac_comb>.
-/
public theorem_wanted diracComb_toTemperedDistribution :
    ∃ T : 𝓢'(ℝ, ℂ), ∀ g : 𝓢(ℝ, ℂ), T g = ∑' n : ℤ, g (n : ℝ)

end MathlibExt.Analysis.Distribution.TemperedExamplesWanted
