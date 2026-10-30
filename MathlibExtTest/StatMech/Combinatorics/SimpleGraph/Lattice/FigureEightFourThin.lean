/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FigureEightFourThin

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.FigureEightFourThin`

* `wpc_fig8_refutation_package`: the figure-eight walk is 4-thin, has interior sites `(1, 1)` and
  `(3, 3)`, a king separation, and violates `cat_CrossArcThick`.
* Consequently `cat_kingInteriorConnected_of_fourThin`-style hypotheses fail for it.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FigureEightFourThin

example : mci_FourThin wpc_fig8 := wpc_fig8_fourThin

example : ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) := wpc_not_noKingSeparation

example : ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) := wpc_cat_crossArcThick_false

example : ksc_KingSaturated wpc_fig8 {(![1, 1] : Site 2)} := wpc_fig8_singleton_saturated

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FigureEightFourThin
