/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.DiscreteJordanSeparation
public import MathlibExt.Probability.Percolation.DiscreteJordanSeparationFalse

/-!
# Tests for `MathlibExt.Probability.Percolation.DiscreteJordanSeparation`

* `DiscreteJordanSeparation` is false (`djsf_djs_is_false`, restated), so no test instantiates
  it. The true statement it was meant to approximate for edges (each edge of a face-boundary graph
  lies on a cycle) is tested in the tests of `DiscreteJordanSeparationVariant`.
-/

@[expose] public section

open StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.DiscreteJordanSeparation

example : ¬ DiscreteJordanSeparation := djsf_djs_is_false

end MathlibExtTest.StatMech.Probability.Percolation.DiscreteJordanSeparation
