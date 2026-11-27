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

`continuous_sleDriving` for the continuous sample path `B_t = t` with `κ = 4`.
-/

@[expose] public section

open StatMech.SLE Set

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.ChainCapacity

example : Continuous (sleDriving 4 (fun t (_ : Unit) => t) ()) :=
  continuous_sleDriving 4 _ () continuous_id

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.ChainCapacity
