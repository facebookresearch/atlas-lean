/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.InformationTheory.DobrushinContraction

/-!
# Strong data processing for Kullback-Leibler divergence: wishlist

`MathlibExt.InformationTheory.DobrushinContraction` proves that a Markov kernel `κ` contracts
total variation by Dobrushin's coefficient `η_TV(κ) = sup_{x, x'} TV(κ x, κ x')`. The same
coefficient bounds the contraction of every f-divergence, in particular of the
Kullback-Leibler divergence: `D(κ ∘ μ ‖ κ ∘ ν) ≤ η_TV(κ) D(μ ‖ ν)`. Its proof (Cohen, Kemperman
and Zbăganu) writes `D_f` as an integral of hockey-stick divergences, each contracted by
`η_TV`, and is not formalized here. The statement is restricted to finite alphabets, the
setting of the cited proof.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Theorem 33.6(a) (`η_f ≤ η_TV`).
* J. E. Cohen, J. H. B. Kemperman and G. Zbăganu, *Comparisons of Stochastic Matrices with
  Applications in Information Theory, Statistics, Economics and Population Sciences*,
  Birkhäuser, 1998.
-/

namespace MathlibExt.InformationTheory.StrongDataProcessingWanted

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.InformationTheory.DobrushinContraction

/-- **Strong data-processing inequality for KL divergence** (`η_KL ≤ η_TV`). For a Markov kernel
`κ` between finite alphabets with measurable singletons and probability measures `μ`, `ν`,
`D(κ ∘ₘ μ ‖ κ ∘ₘ ν) ≤ η_TV(κ) · D(μ ‖ ν)`, where `η_TV(κ) = dobrushinCoeff κ`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 33.6(a) with `f(x) = x log x`; J. E. Cohen, J. H. B. Kemperman
and G. Zbăganu (1998). -/
public theorem_wanted klDiv_comp_le_dobrushinCoeff_mul {X Y : Type*} [Finite X] [Finite Y]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (κ : Kernel X Y) [IsMarkovKernel κ] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤
      ENNReal.ofReal (dobrushinCoeff κ) * _root_.InformationTheory.klDiv μ ν

end

end MathlibExt.InformationTheory.StrongDataProcessingWanted
