/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerSwapInjection

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerSwapInjection`

* `swapGlue` evaluated on constant configurations.
* `r2k_swapInjection_rbi`: `rbi_A`, `rbi_B` have a swap injection; hence Reimer's inequality for
  them under the uniform weight on `Fin 2` (`r2k_reimer_wprob_of_swapInjection`).
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerSwapInjection

/-- The uniform weight on `Fin 2`. -/
noncomputable def w2 : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

lemma w2_nonneg : ∀ i b, 0 ≤ w2 i b := fun _ _ => by norm_num [w2]

lemma w2_prob : ∀ i, w2 i false + w2 i true = 1 := fun _ => by norm_num [w2]

example : swapGlue (fun _ : Fin 2 => true) (fun _ => true) (fun _ => false) = fun _ => false := rfl

example : r2k_SwapInjection rbi_A rbi_B := r2k_swapInjection_rbi

/-- Reimer's inequality for `rbi_A`, `rbi_B` and the uniform weight, via the swap injection. -/
example : wprob w2 (disjointOccurrence rbi_A rbi_B) ≤ wprob w2 rbi_A * wprob w2 rbi_B :=
  r2k_reimer_wprob_of_swapInjection w2 w2_nonneg w2_prob r2k_swapInjection_rbi

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerSwapInjection
