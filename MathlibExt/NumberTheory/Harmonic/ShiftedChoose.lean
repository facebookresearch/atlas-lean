/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Shifted binomial asymptotics

Shifting the upper index by the fixed lower index leaves the leading term unchanged.

## References

* Mathlib, `Mathlib.Analysis.SpecialFunctions.Choose`: `isEquivalent_choose` gives the
  unshifted estimate used here.
* Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1,
  pp. 1–16, Lemmas 1 and 13 (the hyperharmonic asymptotics that use the estimate here).
-/

namespace MetaMathlibExt

open Asymptotics Filter

/-- For fixed $d$, the shifted binomial coefficient $\binom{n+d}{d}$ is asymptotically
equivalent to $n^d/d!$ as $n$ tends to infinity. -/
public theorem isEquivalent_add_choose (d : ℕ) :
    (fun n : ℕ ↦ ((n + d).choose d : ℝ)) ~[atTop] fun n : ℕ ↦ (n : ℝ) ^ d / d.factorial := by
  have shift : (fun n : ℕ ↦ (n : ℝ)) ~[atTop] (fun n ↦ ((n + d : ℕ) : ℝ)) := by
    apply isEquivalent_of_tendsto_one
    simpa [Pi.div_def] using tendsto_natCast_div_add_atTop (d : ℝ)
  exact ((isEquivalent_choose d).comp_tendsto (tendsto_add_atTop_nat d)).trans
    ((shift.symm.pow d).div (IsEquivalent.refl (u := fun _ ↦ (d.factorial : ℝ))))

end MetaMathlibExt
