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
* `IsCapacityParametrized.coeff_zero` and `chordalSLE_hcap_eq` are stated for an arbitrary
  capacity-parametrized chain; no concrete `LoewnerChain` with proved capacity hypotheses is
  available (see the report), so these are checked only as statements.
-/

@[expose] public section

open StatMech.SLE Set

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.ChainCapacity

example : Continuous (sleDriving 4 (fun t (_ : Unit) => t) ()) :=
  continuous_sleDriving 4 _ () continuous_id

example (c : CapacityParametrizedChain) : c.coeff 0 = 0 := c.capacity.coeff_zero

example (c : CapacityParametrizedChain) : ∀ t ∈ Ici (0 : ℝ), c.coeff t = 2 * t :=
  chordalSLE_hcap_eq c

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.ChainCapacity
