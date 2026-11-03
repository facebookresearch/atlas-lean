/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.ChainCapacity

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.ChainCapacity`

* `continuous_sleDriving` for a continuous sample path.
* `loewnerChain_of_sle_realization` projects back to the given maps and driving function.

Removed with the capacity-parametrized package: the former examples stating
`c.coeff 0 = 0` and `c.coeff t = 2 * t` for an arbitrary capacity-parametrized chain.
Those followed only from the assumed capacity rate `a₁' = 2`, not from the Loewner equation.
-/

@[expose] public section

open StatMech.SLE Set

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.ChainCapacity

example : Continuous (sleDriving 4 (fun t (_ : Unit) => t) ()) :=
  continuous_sleDriving 4 _ () continuous_id

example (g : ℝ → ℂ → ℂ)
    (hloe : SatisfiesLoewnerEquation (sleDriving 4 (fun t (_ : Unit) => t) ()) g) :
    (loewnerChain_of_sle_realization 4 (fun t (_ : Unit) => t) () g continuous_id hloe).maps = g :=
  loewnerChain_of_sle_realization_maps 4 _ () g continuous_id hloe

example (g : ℝ → ℂ → ℂ)
    (hloe : SatisfiesLoewnerEquation (sleDriving 4 (fun t (_ : Unit) => t) ()) g) :
    (loewnerChain_of_sle_realization 4 (fun t (_ : Unit) => t) () g continuous_id hloe).driving
      = sleDriving 4 (fun t (_ : Unit) => t) () :=
  loewnerChain_of_sle_realization_driving 4 _ () g continuous_id hloe

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.ChainCapacity
