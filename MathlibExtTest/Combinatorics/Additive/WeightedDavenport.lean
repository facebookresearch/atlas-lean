/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.WeightedDavenport

namespace MetaMathlibExt

/-- The trivial group: one term always gives a weighted zero sum. -/
example : weightedDavenport {1, 2} (ZMod 1) = 1 :=
  weightedDavenport_zmod_one _ ⟨1, by simp⟩

/-- The ordinary Davenport constant of `ZMod 2`. -/
example : weightedDavenport {1} (ZMod 2) = 2 :=
  weightedDavenport_singleton_one_zmod_two

/-- With no weights nothing is a weighted zero sum, so no length forces one: `D_∅(G) = ⊤`. -/
example : weightedDavenport ∅ (ZMod 2) = ⊤ :=
  weightedDavenport_eq_top_iff.mpr fun ℓ => ⟨List.replicate ℓ 0, List.length_replicate,
    fun _ hI _ ha => absurd (ha _ hI.choose_spec) (by simp)⟩

/-- Upper and lower bounds pin `D_{1}(ZMod 2) = 2` through the public API: the one-term
sequence `[1]` is zero-sum free, so `1 < D`, and every length-`2` sequence has a zero sum. -/
example (h2 : ∀ s : List (ZMod 2), s.length = 2 → ¬ IsWeightedZeroSumFree {1} s)
    (h1 : IsWeightedZeroSumFree {1} [(1 : ZMod 2)]) : weightedDavenport {1} (ZMod 2) = 2 :=
  le_antisymm (weightedDavenport_le h2) (Order.add_one_le_of_lt (lt_weightedDavenport h1))

end MetaMathlibExt
