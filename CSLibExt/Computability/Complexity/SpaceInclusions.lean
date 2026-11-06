/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Machines.Turing.MultiTape.TimeFromSpace

/-!
# Polynomial space is contained in exponential time

A polynomial-space decider already halts on every input. Its readable
configuration cores cannot repeat before the first halt, so the same machine
runs in exponential time. The configuration bound includes the input head,
but not the write-only output tape. No simulation or new machine model is
needed.

The fixed machine and space polynomial determine all time constants before
any input is chosen. The affine time allowance also covers input lengths zero
and one, including constant and zero space bounds.

The classes are those of `Cslib.Complexity.Classes`, using CSLib's canonical
multi-tape machines. The promoted theorem keeps its original public name.
-/

@[expose] public section

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

private theorem exponential_bound (a c c₁ c₂ d : ℕ) :
    ∃ D A B : ℕ, ∀ n : ℕ,
      (n + 2) * a * 2 ^ (c * (c₁ * n ^ d + c₂)) ≤
        A * 2 ^ (n ^ D) + B := by
  refine ⟨d + 1 + (c * c₁ + 1), 2 * a * 2 ^ (c * c₂),
    3 * a * 2 ^ (c * (c₁ + c₂)), fun n => ?_⟩
  by_cases hn : n ≤ 1
  · have hp : n ^ d ≤ 1 := by
      simpa using Nat.pow_le_pow_left hn d
    have he : c * (c₁ * n ^ d + c₂) ≤ c * (c₁ + c₂) := by
      exact Nat.mul_le_mul_left c
        (Nat.add_le_add_right (by simpa using Nat.mul_le_mul_left c₁ hp) c₂)
    have hb : (n + 2) * a * 2 ^ (c * (c₁ * n ^ d + c₂)) ≤
        3 * a * 2 ^ (c * (c₁ + c₂)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right a (by omega))
        (Nat.pow_le_pow_right (by decide) he)
    exact hb.trans (Nat.le_add_left _ _)
  · have hn₁ : 1 ≤ n := by omega
    have hm : c * c₁ + 1 ≤ n ^ (c * c₁ + 1) :=
      (Nat.lt_pow_self (by omega)).le
    have hp : n ^ d ≤ n ^ (d + 1) :=
      Nat.pow_le_pow_right hn₁ (Nat.le_succ d)
    have he : n + c * c₁ * n ^ d ≤ n ^ (d + 1 + (c * c₁ + 1)) := by
      calc
        n + c * c₁ * n ^ d ≤
            n ^ (d + 1) + c * c₁ * n ^ (d + 1) :=
          Nat.add_le_add (Nat.le_pow (by omega))
            (Nat.mul_le_mul_left _ hp)
        _ = n ^ (d + 1) * (c * c₁ + 1) := by ring
        _ ≤ n ^ (d + 1) * n ^ (c * c₁ + 1) :=
          Nat.mul_le_mul_left _ hm
        _ = n ^ (d + 1 + (c * c₁ + 1)) := (pow_add _ _ _).symm
    have hn₂ : n + 2 ≤ 2 * 2 ^ n := by
      have h : n < 2 ^ n := Nat.lt_two_pow_self
      omega
    calc
      (n + 2) * a * 2 ^ (c * (c₁ * n ^ d + c₂)) ≤
          (2 * 2 ^ n) * a * 2 ^ (c * (c₁ * n ^ d + c₂)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right a hn₂)
      _ = (2 * a * 2 ^ (c * c₂)) * 2 ^ (n + c * c₁ * n ^ d) := by
        rw [Nat.mul_add, pow_add, pow_add]
        ring
      _ ≤ (2 * a * 2 ^ (c * c₂)) *
          2 ^ (n ^ (d + 1 + (c * c₁ + 1))) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) he)
      _ ≤ _ := Nat.le_add_right _ _

/-- **Polynomial-space decider runs in exponential time.**
The same finite polynomial-space decider has an exponential time bound.
All constants precede every input. Halting comes from `Decides`, not space. -/
theorem SpaceBoundedBy.exists_exponential_timeBoundedBy
    {k : ℕ} {State : Type*} [Finite State]
    {tm : MultiTapeTM k Bool State} {L : Set (List Bool)} {c₁ c₂ d : ℕ}
    (hs : SpaceBoundedBy tm (fun n => c₁ * n ^ d + c₂))
    (hd : Decides tm L) :
    ∃ D A B : ℕ, TimeBoundedBy tm (fun n => A * 2 ^ (n ^ D) + B) := by
  obtain ⟨a, c, hb⟩ := exists_exponential_time_bound tm
  obtain ⟨D, A, B, hbound⟩ := exponential_bound a c c₁ c₂ d
  refine ⟨D, A, B, fun w => ?_⟩
  obtain ⟨t, ht, _⟩ := hd w
  exact (hb w _ (hs w) ⟨t, ht⟩).mono (hbound w.length)

end Cslib.Turing.MultiTapeTM

namespace MetaMathlibExt.Complexity.KeyTheorems.PSPACESubsetEXP

open Cslib.Complexity.Classes Cslib.Turing.MultiTapeTM

/-- **PSPACE is contained in EXP.**
Every canonical polynomial-space language is in exponential time,
using its original finite multi-tape decider.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach,
Cambridge University Press, 2009, Chapter 4 (Space complexity). -/
theorem pspace_subset_exp : PSPACE ⊆ EXP := by
  intro L hL
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨c₁, c₂, k, State, hS, tm, hdec, hs, _⟩ := mem_DSPACE_iff.mp hd
  obtain ⟨D, A, B, ht⟩ := hs.exists_exponential_timeBoundedBy hdec
  exact ⟨D, mem_DTIME_iff.mpr
    ⟨A, B, k, State, hS, tm, hdec, ht, _, hs⟩⟩

end MetaMathlibExt.Complexity.KeyTheorems.PSPACESubsetEXP
