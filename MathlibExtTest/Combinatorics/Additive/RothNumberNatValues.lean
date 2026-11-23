/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Additive.RothNumberNatValues

namespace MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted

-- The first value gives a four-element progression-free subset of the interval of length five.
example : ∃ s ⊆ Finset.range 5, s.card = 4 ∧ ThreeAPFree (s : Set ℕ) := by
  have h₅ : rothNumberNat 5 = 4 :=
    congrArg (fun l : List ℕ => l[0]!) rothNumberNat_five_to_fourteen
  simpa only [h₅] using rothNumberNat_spec 5

-- The last value forces a nontrivial progression as soon as a ninth element is present.
example {s : Finset ℕ} (hs : s ⊆ Finset.range 14) (hcard : 8 < s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a + c = b + b ∧ a ≠ b := by
  have h₁₄ := congrArg (fun l : List ℕ => l[9]!) rothNumberNat_five_to_fourteen
  change rothNumberNat 14 = 8 at h₁₄
  by_contra! h
  have hfree : ThreeAPFree (s : Set ℕ) := fun _ ha _ hb _ hc => h _ ha _ hb _ hc
  have hle := hfree.le_addRothNumber hs
  rw [← rothNumberNat_def, h₁₄] at hle
  exact hcard.not_ge hle

end MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted
