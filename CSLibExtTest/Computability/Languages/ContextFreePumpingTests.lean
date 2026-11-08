/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Pumping

/-!
# Ordinary-client tests for the CFL pumping lemma
-/

public section

namespace Cslib.Language.ContextFreePumpingTests

/-- Every context-free language has a positive pumping length,
exercised on the empty language. -/
theorem zeroLanguage_pumping_length_pos :
    ∃ n : ℕ, 0 < n := by
  obtain ⟨n, hn, -⟩ := IsContextFree.pumping (IsContextFree.zero (T := Bool))
  exact ⟨n, hn⟩

/-- Pumping down (`i = 0`) and pumping twice (`i = 2`), derived from
the pumping lemma as an ordinary client would. -/
theorem pumping_zero_two {L : Language Bool} (hL : L.IsContextFree) :
    ∃ n : ℕ, 0 < n ∧ ∀ w ∈ L, n ≤ w.length →
      ∃ u v x y z : List Bool, w = u ++ v ++ x ++ y ++ z ∧
        v ++ y ≠ [] ∧ (v ++ x ++ y).length ≤ n ∧
        u ++ x ++ z ∈ L ∧ u ++ v ++ v ++ x ++ y ++ y ++ z ∈ L := by
  obtain ⟨n, hn, hpump⟩ := IsContextFree.pumping hL
  refine ⟨n, hn, fun w hw hlen => ?_⟩
  obtain ⟨u, v, x, y, z, hsplit, hvy, hvxy, hi⟩ := hpump w hw hlen
  refine ⟨u, v, x, y, z, hsplit, hvy, hvxy, ?_, ?_⟩
  · simpa using hi 0
  · have h2 := hi 2
    simp only [List.replicate_succ, List.replicate_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil] at h2
    simpa [List.append_assoc] using h2

end Cslib.Language.ContextFreePumpingTests
