/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexCounterexample

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexCounterexample`

* `shbK4H_ssubset_shbK4G`: the smaller edge domain is a proper subset;
* `shbK4_rhos_at_two_thirds`: the explicit values `54/145` and `86/225`;
* `shb_supportLex_edgeDomain_P3_counterexample`: `ρ` increases with the domain (P3 fails), and it
  agrees with the explicit values.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexCounterexample

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.shbK4Edge

-- The domain inclusion is proper.
example : shbK4H ⊂ shbK4G := shbK4H_ssubset_shbK4G

-- The explicit values at `x = 2/3`.
example : shbK4DirectRho shbK4H (2 / 3) = 54 / 145 ∧ shbK4DirectRho shbK4G (2 / 3) = 86 / 225 :=
  shbK4_rhos_at_two_thirds

-- Domain monotonicity fails.
example : shbK4DirectRho shbK4H (2 / 3) < shbK4DirectRho shbK4G (2 / 3) :=
  shb_supportLex_edgeDomain_P3_counterexample

-- The failure is visible on the explicit values.
example : (54 / 145 : ℚ) < 86 / 225 := by norm_num

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexCounterexample
