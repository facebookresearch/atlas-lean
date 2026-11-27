/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem1196
import Mathlib.Data.Nat.Prime.Basic

namespace MathlibExtTest.NumberTheory.ErdosProblem1196

open MathlibExt.NumberTheory.ErdosProblem1196Wanted

-- The set of all primes is an infinite primitive set above the cutoff 2.
example : Summable (fun a : {n : ℕ | n.Prime} ↦ 1 / ((a.val : ℝ).log * a)) := by
  obtain ⟨_, _, h⟩ := conjecture_holds
  refine (h 2 (by decide) {n | n.Prime} (fun _ hn ↦ hn.two_le) ?_).1
  intro a ha b hb hd
  exact associated_iff_eq.mpr ((Nat.dvd_prime hb).mp hd |>.resolve_left ha.ne_one)

-- At the smallest cutoff, the singleton consisting of 1 contributes zero.
example : ∃ o : ℕ → ℝ, 0 < 1 + o 1 ∧
    (∑' (a : ({1} : Set ℕ)), 1 / ((a.val : ℝ).log * a)) = 0 := by
  obtain ⟨o, _, h⟩ := conjecture_holds
  have hz : ∀ a : ({1} : Set ℕ), 1 / ((a.val : ℝ).log * a) = 0 := by
    intro ⟨n, hn⟩
    have hn' : n = 1 := hn
    simp [hn']
  have hzero : (∑' (a : ({1} : Set ℕ)), 1 / ((a.val : ℝ).log * a)) = 0 := by simp [hz]
  have hsubset : ({1} : Set ℕ) ⊆ Set.Ici 1 := fun _ hn ↦ le_of_eq hn.symm
  have hprim : IsPrimitive ({1} : Set ℕ) := by
    intro a ha b hb _
    exact associated_iff_eq.mpr (ha.trans hb.symm)
  exact ⟨o, hzero ▸ (h 1 Nat.one_pos _ hsubset hprim).2, hzero⟩

end MathlibExtTest.NumberTheory.ErdosProblem1196
