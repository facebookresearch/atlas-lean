/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing

/-!
# Duplicate polarized-key splitting is rejected
-/

namespace Cslib.SessionTypes.Endpoint.DuplicateTests

/-- Two copies of the same active role cannot be a linear parallel split. -/
theorem duplicate_key_split_rejected (e : Key) :
    ¬ Finmap.Disjoint (Finmap.singleton e (⟨0, .sendName .done⟩ : Capability) : Context)
      (Finmap.singleton e (⟨0, .sendName .done⟩ : Capability) : Context) := by
  intro h
  exact h e (by simp) (by simp)

/-- Two output threads cannot both consume a single owned active role. -/
theorem duplicate_output_role_rejected (b : PiCalculus.Name) :
    ¬ HasType 0 (Finmap.singleton (⟨.const 0, .positive⟩ : Key) ⟨0, .sendName .done⟩)
      (.par (.out (.const 0) b .nil) (.out (.const 0) b .nil)) := by
  intro h
  obtain ⟨Δ, Θ, heq, hd, hl, hr⟩ := h.par_inv
  obtain ⟨r, c, hc⟩ := hl.out_owned
  obtain ⟨s, t, ht⟩ := hr.out_owned
  have hcl := Finmap.mem_of_lookup_eq_some hc
  have htr := Finmap.mem_of_lookup_eq_some ht
  have hmL : (⟨.const 0, r⟩ : Key) ∈
      (Finmap.singleton (⟨.const 0, .positive⟩ : Key) ⟨0, .sendName .done⟩ : Context) := by
    rw [heq]
    exact Finmap.mem_union.mpr (Or.inl hcl)
  have hmR : (⟨.const 0, s⟩ : Key) ∈
      (Finmap.singleton (⟨.const 0, .positive⟩ : Key) ⟨0, .sendName .done⟩ : Context) := by
    rw [heq]
    exact Finmap.mem_union.mpr (Or.inr htr)
  have hL := (Finmap.mem_singleton _ _ _).mp hmL
  have hR := (Finmap.mem_singleton _ _ _).mp hmR
  exact hd _ hcl ((hL.trans hR.symm).symm ▸ htr)

end Cslib.SessionTypes.Endpoint.DuplicateTests
