/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Real.Basic

/-! A finite permutation preserving all nonzero signed coefficients also preserves the zero rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Genuine finite signed transport on the nonzero support determines every remaining zero row. -/
theorem generatedSixth_xi_signed_support_complete {I : Type*} [Finite I]
    (σ : Equiv.Perm I) (w X : I → ℝ) (hw : ∀ r, w r ≠ 0)
    (h : ∀ r, X r ≠ 0 → w r * X r = X (σ r)) :
    ∀ r, w r * X r = X (σ r) := by
  let S := {r : I // X r ≠ 0}
  let f : S → S := fun r => ⟨σ r.val, by
    rw [← h r.val r.property]
    exact mul_ne_zero (hw r.val) r.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply σ.injective
    exact congrArg Subtype.val hab
  have hs : Function.Surjective f := Finite.surjective_of_injective hf
  intro r
  by_cases hr : X r = 0
  · have hz : X (σ r) = 0 := by
      by_contra hn
      obtain ⟨t, ht⟩ := hs ⟨σ r, hn⟩
      have he : t.val = r := σ.injective (congrArg Subtype.val ht)
      exact t.property (he ▸ hr)
    rw [hr, hz, mul_zero]
  · exact h r hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
