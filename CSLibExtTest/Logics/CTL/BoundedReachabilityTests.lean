/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.CTL.BoundedReachability

/-! # Regressions for the diameter completeness threshold -/

set_option autoImplicit false

namespace CSLibExtTest.Logics.CTL.BoundedReachability

open Cslib Cslib.CTL

private def chain : LTS (Fin 3) Unit where
  Tr s _ t := t.val = s.val + 1

private theorem chain_length {s t : Fin 3} {labels : List Unit}
    (h : chain.MTr s labels t) : t.val = s.val + labels.length := by
  induction h with
  | refl => simp
  | stepL hstep _ ih =>
      change _ = _ + 1 at hstep
      simp only [List.length_cons]
      omega

private theorem chain_trace_two : chain.MTr 0 [(), ()] 2 :=
  .stepL (s2 := 1) rfl (.stepL (s2 := 2) rfl .refl)

private theorem chain_reaches_two : chain.CanReach 0 2 :=
  ⟨_, chain_trace_two⟩

-- The full chain is a shortest path of length two; no path can have length three.
example : chain.diameter = 2 := by
  have hleast := chain.isLeast_diameterBound
  apply le_antisymm
  · apply hleast.2
    intro s t labels hlen htrace
    have hlen' := chain_length htrace
    have ht := t.isLt
    omega
  · obtain ⟨labels, hlen, htrace⟩ := LTS.DiameterBound.shorten chain hleast.1 chain_reaches_two
    have h := chain_length htrace
    change 2 = 0 + labels.length at h
    omega

private def target (s : Fin 3) (_ : Unit) : Prop := s = 2

example : existsFinallyAtLength chain target {0} (.atom ()) 2 := by
  obtain ⟨ss, h₀, hk, hrun⟩ := LTS.exists_finiteRun_of_mtr chain_trace_two
  exact ⟨ss, by simp [h₀], hrun, hk⟩

-- A deadlocked initial state satisfies the target at length zero, but cannot
-- supply a positive-length witness, even though the system diameter is positive.
example : existsFinallyAtLength chain target {2} (.atom ()) 0 ∧
    ∀ k, 0 < k → ¬ existsFinallyAtLength chain target {2} (.atom ()) k := by
  constructor
  · exact ⟨fun _ => 2, by simp, LTS.finiteRun_zero, rfl⟩
  · rintro k hk ⟨ss, h₀, hrun, _⟩
    have he : ss 0 = 2 := by simpa using h₀
    obtain ⟨a, hstep⟩ := hrun 0 hk
    change (ss 1).val = (ss 0).val + 1 at hstep
    rw [he] at hstep
    have hlt := (ss 1).isLt
    change (ss 1).val = 2 + 1 at hstep
    omega

private def toggle : LTS Bool Unit where
  Tr s _ t := t = !s

-- In the cycle every two-step walk returns to its origin, so the shortening
-- condition is nonvacuous and uses an empty path as the replacement.
private theorem toggle_bound : toggle.DiameterBound 1 := by
  intro s t labels hlen htrace
  cases labels with
  | nil => simp at hlen
  | cons a tail =>
      cases tail with
      | nil => simp at hlen
      | cons b tail =>
          obtain ⟨mid, h₁, hm⟩ := LTS.MTr.cons_iff.mp htrace
          obtain ⟨last, h₂, ht⟩ := LTS.MTr.cons_iff.mp hm
          have hnil : tail = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
          subst tail
          have hl := LTS.MTr.nil_eq toggle ht
          change mid = !s at h₁
          change last = !mid at h₂
          have he : t = s := by rw [← hl, h₂, h₁]; simp
          refine ⟨[], by decide, ?_⟩
          rw [he]
          exact .refl

example :
    (∃ s ∈ ({false} : Set Bool),
      Satisfies toggle (fun b (_ : Unit) => b = true) s (Formula.atom ()).existsFinally) ↔
      ∃ k ≤ 1, existsFinallyAtLength toggle (fun b (_ : Unit) => b = true) {false} (.atom ()) k :=
  existsFinally_iff_exists_le_of_diameterBound toggle_bound _ _

end CSLibExtTest.Logics.CTL.BoundedReachability
