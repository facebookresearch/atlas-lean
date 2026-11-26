/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Dynamics.SymbolicDynamics.AperiodicConjugacy

namespace MathlibExt.Dynamics.AMR43Problem1Wanted

open SymbolicDynamics.FullShift

private theorem not_periodic_of_unique_symbol {N : ℕ} {x : FullShiftSpace N}
    {c : Fin N} (hc : ∀ i, x i = c ↔ i = 0) : x ∉ Function.periodicPts (unitShift N) := by
  intro hx
  obtain ⟨n, hn, hper⟩ := Function.mem_periodicPts.mp hx
  have hshift (m : ℕ) (i : ℤ) : (unitShift N)^[m] x i = x ((m : ℤ) + i) := by
    induction m generalizing i with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', unitShift_apply, ih]
      congr 1
      omega
  have heq := congrFun (show (unitShift N)^[n] x = x from hper) 0
  rw [hshift, add_zero] at heq
  have hn₀ := (hc n).mp (heq.trans ((hc 0).mpr rfl))
  omega

private def binaryPoint : ↥AperiodicX :=
  ⟨fun i ↦ if i = 0 then 1 else 0, not_periodic_of_unique_symbol (c := 1) (by
    intro i
    by_cases hi : i = 0 <;> simp [hi])⟩

private def colouring (i : ℤ) : Fin 3 :=
  if i = 0 then 2 else if i % 2 = 0 then 0 else 1

private def colouredPoint : ↥AperiodicY := by
  refine ⟨colouring, ?_, not_periodic_of_unique_symbol (c := 2) ?_⟩
  · intro i
    by_cases h₀ : i = 0
    · subst i
      decide
    by_cases h₁ : i + 1 = 0
    · obtain rfl : i = -1 := by omega
      decide
    by_cases h : i % 2 = 0
    · have h' : (i + 1) % 2 ≠ 0 := by omega
      simp [colouring, h₀, h₁, h, h']
    · have h' : (i + 1) % 2 = 0 := by omega
      simp [colouring, h₀, h₁, h, h']
  · intro i
    by_cases h : i = 0
    · simp [colouring, h]
    · by_cases h' : i % 2 = 0 <;> simp [colouring, h, h']

-- Each aperiodic subspace has a point whose distinguished symbol shifts to the left.
example : (shiftXRes binaryPoint).val (-1) = 1 := by decide
example : (shiftYRes colouredPoint).val (-1) = 2 := by decide

example (e : ↥AperiodicX ≃ₜ ↥AperiodicY)
    (he : ∀ a : ↥AperiodicX, e (shiftXRes a) = shiftYRes (e a)) : False :=
  conjecture_refuted ⟨e, he⟩

end MathlibExt.Dynamics.AMR43Problem1Wanted
