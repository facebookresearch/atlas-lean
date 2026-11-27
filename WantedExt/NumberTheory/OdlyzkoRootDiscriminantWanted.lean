/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace MetaMathlibExt

@[expose] public section

open Module NumberField

/-- **Odlyzko's root discriminant bound in degree at least 18.** Let $K$ be a totally complex
number field of degree $n = [K : \mathbb{Q}] \ge 18$ and discriminant $d_K$. Then
$|d_K| \ge 8.25^n$; equivalently, the root discriminant $|d_K|^{1/n}$ of $K$ is at least $8.25$.

Minkowski's elementary argument is not strong enough; the bound comes from analysing the zeros
of the Dedekind zeta function of $K$.

Source: A. M. Odlyzko, *Bounds for discriminants and related estimates for
class numbers, regulators and zeros of zeta functions: a survey of recent
results*, Sém. Delange-Pisot-Poitou 18(1) (1976–1977), exp. 6,
<https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/>. -/
theorem_wanted odlyzko_root_discr_ge (K : Type*) [Field K] [NumberField K]
    [IsTotallyComplex K] (hdim : finrank ℚ K ≥ 18) :
    |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K

end

end MetaMathlibExt
