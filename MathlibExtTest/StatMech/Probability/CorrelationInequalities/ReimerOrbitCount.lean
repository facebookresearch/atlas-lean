/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerOrbitCount

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerOrbitCount`

* `orbitKey` on a pair of constant configurations.
* `PerOrbitCard rbi_A rbi_B` (`perOrbitCard_rbi`) and the resulting Reimer inequality
  (`reimer_wprob_of_perOrbitCard`) under the uniform weight on `Fin 2`.
* `r2k_swapInjection_iff_perOrbitCard` on `rbi_A`, `rbi_B`.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerOrbitCount

/-- The uniform weight on `Fin 2`. -/
noncomputable def w2 : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

lemma w2_nonneg : ∀ i b, 0 ≤ w2 i b := fun _ _ => by norm_num [w2]

lemma w2_prob : ∀ i, w2 i false + w2 i true = 1 := fun _ => by norm_num [w2]

example : orbitKey ((fun _ => true, fun _ => false) : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) =
    (fun _ => true, fun _ => false) := rfl

example : PerOrbitCard rbi_A rbi_B := perOrbitCard_rbi

example : wprob w2 (disjointOccurrence rbi_A rbi_B) ≤ wprob w2 rbi_A * wprob w2 rbi_B :=
  reimer_wprob_of_perOrbitCard w2 w2_nonneg w2_prob perOrbitCard_rbi

example : r2k_SwapInjection rbi_A rbi_B ↔ PerOrbitCard rbi_A rbi_B :=
  r2k_swapInjection_iff_perOrbitCard _ _

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerOrbitCount
