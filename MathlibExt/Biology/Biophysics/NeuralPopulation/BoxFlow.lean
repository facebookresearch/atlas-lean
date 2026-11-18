/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Box projection for rate dynamics

The coordinatewise box projection is Mathlib's canonical interval projection `Set.projIcc`: its value lies in the interval by construction, and it is the identity on points already in the interval.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-- The box projection onto `[0, U]`, as the canonical interval
projection. Membership in the box is part of the subtype. -/
noncomputable def boxProj (U : ℝ) (hU : 0 ≤ U) (x : ℝ) : Set.Icc (0:ℝ) U :=
  Set.projIcc 0 U hU x

/-- The projected value as a real number is `max 0 (min U x)`. -/
lemma boxProj_coe (U : ℝ) (hU : 0 ≤ U) (x : ℝ) :
    ((boxProj U hU x : Set.Icc (0:ℝ) U) : ℝ) = max 0 (min U x) :=
  Set.coe_projIcc 0 U hU x

/-- The projection is the identity on points already in the box. -/
lemma boxProj_of_mem (U : ℝ) (hU : 0 ≤ U) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) U) : boxProj U hU x = ⟨x, hx⟩ :=
  Set.projIcc_of_mem hU hx

end MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow
