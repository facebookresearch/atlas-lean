/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.PlanarDualCutConnected
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.PlanarDualCutConnected`

* `pdc_rot90Iso`: the quarter turn maps the primal barrier graph isomorphically onto the rotated
  barrier graph (applied to a point).
* The refutation `pdc_allClosed_not_DualCutConnectsRot` (with `pdc_allClosed_noH`): for `n = 3` the
  all-closed configuration has no horizontal crossing but no rotated cut connection.
* `pdc_primalConnects_iff_DualCutConnectsRot`.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.PlanarDualCutConnected

example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (a : Site 2) : pdc_rot90Iso ω n a = rot90Fun a := rfl

example : ¬ HorizontalCrossing (fun _ => false) 0 3 0 3 := pdc_allClosed_noH 3 (by norm_num)

example : ¬ dcp_DualCutConnectsRot (fun _ => false) 3 :=
  pdc_allClosed_not_DualCutConnectsRot 3 (by norm_num)

example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pdc_PrimalBarrierConnects ω n ↔ dcp_DualCutConnectsRot ω n :=
  pdc_primalConnects_iff_DualCutConnectsRot ω n

end MathlibExtTest.StatMech.Probability.Percolation.Universality.PlanarDualCutConnected
