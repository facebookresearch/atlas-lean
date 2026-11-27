/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RamseyFamilyDecreasingSequenceIdempotent

/-! # Tests for idempotents from decreasing sequences in Ramsey families -/

namespace MathlibExtTest.RamseyFamilyDecreasingSequenceIdempotent

open MetaMathlibExt

attribute [local instance] Ultrafilter.semigroup

-- A strictly decreasing sequence of tails yields an idempotent containing a proper set.
example : ∃ p : Ultrafilter ℕ, p * p = p ∧ Set.Ici (2 : ℕ) ∈ p := by
  have hF : IsRamseyFamily {B : Set ℕ | B.Nonempty} :=
    ⟨⟨Set.univ, Set.univ_nonempty⟩, Set.not_nonempty_empty,
      fun _ _ hB hBD => hB.mono hBD, fun _ _ hBD => Set.union_nonempty.mp hBD⟩
  let C (n : ℕ) := Set.Ici (n + 2)
  have hshift : ∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : ℕ | x * y ∈ C n} := by
    intro n x hx
    refine ⟨n, fun y hy => ?_⟩
    have hx' : 1 ≤ x := le_trans (by omega : 1 ≤ n + 2) hx
    change n + 2 ≤ x * y
    exact le_trans hy (by simpa only [one_mul] using Nat.mul_le_mul_right y hx')
  obtain ⟨p, _, hpp, hpA⟩ := exists_idempotent_mem_of_decreasing_sequence hF
    (by simp [betaFamily_nonempty_sets]) (A := Set.Ici 2) C
    (fun _ _ hij _ hy => (Nat.add_le_add_right hij 2).trans hy)
    (fun n _ hy => (Nat.le_add_left 2 n).trans hy) hshift (fun n => ⟨n + 2, Set.mem_Ici.mpr le_rfl⟩)
  exact ⟨p, hpp, hpA⟩

local instance : Semigroup Bool where
  mul _ y := y
  mul_assoc _ _ _ := rfl

-- The theorem also retains membership in a proper β(F) in a noncommutative semigroup.
example : ∃ p ∈ betaFamily {B : Set Bool | true ∈ B}, p * p = p ∧ ({true} : Set Bool) ∈ p := by
  have hF : IsRamseyFamily {B : Set Bool | true ∈ B} :=
    ⟨⟨Set.univ, Set.mem_univ true⟩, id, fun _ _ hB hBD => hBD hB, fun _ _ h => h⟩
  have hleft := (betaFamily_isLeftIdeal_iff hF).2 (fun _ _ hB => ⟨true, hB, rfl⟩)
  exact exists_idempotent_mem_of_decreasing_sequence hF (fun p _ q hq => hleft p q hq)
    (fun _ => {true}) (fun _ _ _ => Set.Subset.rfl) (fun _ => Set.Subset.rfl)
    (fun n _ _ => ⟨n, fun _ hy => hy⟩) (fun _ => Set.mem_singleton _)

/-- info: 'MetaMathlibExt.exists_idempotent_mem_of_decreasing_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MetaMathlibExt.exists_idempotent_mem_of_decreasing_sequence

end MathlibExtTest.RamseyFamilyDecreasingSequenceIdempotent
