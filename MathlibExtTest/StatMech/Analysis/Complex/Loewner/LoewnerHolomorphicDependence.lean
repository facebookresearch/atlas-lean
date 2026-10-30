/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerHolomorphicDependence

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.LoewnerHolomorphicDependence`

* `loewnerInitialJacobian` at time `0` is `1` and never vanishes.
* `loewnerMaximalMaps_conformalAt` and `loewnerMaximalMaps_differentiableOn` for the zero driving
  function, at the point `I` and time `1/16` (which lies in the unswallowed domain).
* `loewnerField_hasDerivAt_initial` at `z = I`, `W = 0`.
-/

@[expose] public section

open StatMech.SLE Complex
open UpperHalfPlane (upperHalfPlaneSet)

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerHolomorphicDependence

example (z : ℂ) : loewnerInitialJacobian (fun _ => 0) 0 z = 1 := loewnerInitialJacobian_zero _ _

example (t : ℝ) (z : ℂ) : loewnerInitialJacobian (fun _ => 0) t z ≠ 0 :=
  loewnerInitialJacobian_ne_zero _ _ _

lemma I_mem_unswallowed : I ∈ loewnerUnswallowedDomain (fun _ => 0) (1 / 16) :=
  mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight continuous_const (by norm_num)
    (by simp [UpperHalfPlane.upperHalfPlaneSet]) (by norm_num)

example : ConformalAt (loewnerMaximalMaps (fun _ => 0) (1 / 16)) I :=
  loewnerMaximalMaps_conformalAt continuous_const (by norm_num) I_mem_unswallowed

example : DifferentiableOn ℂ (loewnerMaximalMaps (fun _ => 0) 1)
    (loewnerUnswallowedDomain (fun _ => 0) 1) :=
  loewnerMaximalMaps_differentiableOn continuous_const (by norm_num)

example : HasDerivAt (loewnerField (fun _ => 0) 0) (-2 / (I - ((0 : ℝ) : ℂ)) ^ 2) I :=
  loewnerField_hasDerivAt_initial (fun _ => 0) 0 (by simp)

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerHolomorphicDependence
