/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.OrderIsoNat
import MathlibExt.Combinatorics.AccessibleSets

/-! # Tests for accessible sets and diffsequences -/

namespace MetaMathlibExt.accessible_of_colored_subset_diffsequences

-- Shifting the odds by one gives the positive even gaps. Any two-coloring admits
-- arbitrarily long monochromatic sequences with these gaps.
example : IsRAccessible 2 (Set.range fun n : ℕ => 2 * n + 2) := by
  let D := Set.range fun n : ℕ => 2 * n + 1
  have hshift : {e : ℕ | ∃ d ∈ D, e = d + 1} = Set.range (fun n : ℕ => 2 * n + 2) := by
    ext e
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, rfl⟩
  rw [← hshift]
  apply accessible_of_colored_subset_diffsequences 1 2 (by decide) D
  · rintro _ ⟨n, rfl⟩
    exact Nat.succ_pos _
  · intro χ k _
    let x (i : Fin k) : {n : ℕ+ // (n : ℕ) ∈ D} :=
      ⟨⟨2 * (i : ℕ) + 1, Nat.succ_pos _⟩, i, rfl⟩
    refine ⟨x, fun _ _ => Subsingleton.elim (α := Fin 1) .., ?_⟩
    intro i hi
    refine ⟨2, ⟨1, ⟨0, rfl⟩, rfl⟩, ?_⟩
    simp [x, Nat.mul_add]

end MetaMathlibExt.accessible_of_colored_subset_diffsequences

namespace MetaMathlibExt.two_accessible_of_internal_diffsequences

-- Consecutive powers of two have gaps that are themselves powers of two.
example : IsRAccessible 2 (Set.range fun n : ℕ => 2 ^ n) := by
  apply two_accessible_of_internal_diffsequences
  · rintro _ ⟨n, rfl⟩
    exact pow_pos (by decide : 0 < (2 : ℕ)) n
  · intro k _
    refine ⟨fun i => ⟨2 ^ (i : ℕ), pow_pos (by decide) _⟩, fun i => ⟨i, rfl⟩, ?_⟩
    intro i hi
    refine ⟨2 ^ i, ⟨i, rfl⟩, ?_⟩
    change ((2 ^ (i + 1) : ℕ) : ℤ) - (2 ^ i : ℕ) = (2 ^ i : ℕ)
    simp [pow_succ, mul_two]

end MetaMathlibExt.two_accessible_of_internal_diffsequences

namespace MetaMathlibExt.accessible_divisible_subset

-- Enumerating an infinite color class in order witnesses accessibility of all positive gaps.
private theorem isAccessible_Ioi_zero : IsAccessible (Set.Ioi 0) := by
  intro r hr
  refine ⟨Set.Subset.rfl, hr, ?_⟩
  intro c k _
  obtain ⟨color, hinf⟩ := Finite.exists_infinite_fiber (fun n : ℕ => c n.succPNat)
  let e := Nat.Subtype.orderIsoOfNat ((fun n : ℕ => c n.succPNat) ⁻¹' {color})
  have hc (i : ℕ) : c (e i).val.succPNat = color := (e i).property
  refine ⟨fun i => (e i).val.succPNat, fun i j => (hc i).trans (hc j).symm, ?_⟩
  intro i hi
  have hlt : (e i).val < (e (i + 1)).val := e.strictMono (Nat.lt_succ_self i)
  exact ⟨(e (i + 1)).val - (e i).val, Nat.sub_pos_of_lt hlt, by simp⟩

-- A two-coloring admits arbitrarily long monochromatic sequences with positive gaps divisible by 3.
example : IsRAccessible 2 {a : ℕ | 0 < a ∧ 3 ∣ a} := by
  simpa only [Set.mem_Ioi, Nat.dvd_iff_mod_eq_zero] using
    accessible_divisible_subset (Set.Ioi 0) 3 2 (by decide)
      (isAccessible_Ioi_zero 6 (by decide))

end MetaMathlibExt.accessible_divisible_subset

namespace MetaMathlibExt.accessible_union_partition

-- In the parity partition of an accessible set, the even gaps must be accessible.
example {D : Set ℕ} (hD : IsAccessible D) : IsAccessible {d ∈ D | d % 2 = 0} := by
  have hsplit : D = {d ∈ D | d % 2 = 1} ∪ {d ∈ D | d % 2 = 0} := by
    ext d
    change d ∈ D ↔ (d ∈ D ∧ d % 2 = 1) ∨ (d ∈ D ∧ d % 2 = 0)
    rw [← and_or_left]
    exact ⟨fun hd => ⟨hd, by omega⟩, And.left⟩
  apply (accessible_union_partition _ _ _ hsplit hD).resolve_left
  intro hodd
  let parity (a : ℕ+) : Fin 2 := ⟨(a : ℕ) % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨x, hc, hdiff⟩ := (hodd 2 (by decide)).2.2 parity 2 (by decide)
  obtain ⟨d, ⟨_, hd⟩, hgap⟩ := hdiff 0 (by decide)
  have heq : (x 0 : ℕ) % 2 = (x 1 : ℕ) % 2 := congrArg Fin.val (hc 0 1)
  change (x 1 : ℤ) - (x 0 : ℤ) = d at hgap
  omega

end MetaMathlibExt.accessible_union_partition

namespace MetaMathlibExt.large_union_partition

-- Adjoining every odd gap cannot make a set large, even if it already contains some odd gaps.
example {D : Set ℕ} (h : IsLarge (D ∪ {d : ℕ | d % 2 = 1})) : IsLarge D := by
  apply (large_union_partition _ _ _ rfl h).resolve_right
  intro hodd
  let parity (n : ℕ+) : Fin 2 := ⟨(n : ℕ) % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨x, hx, a, d, hd, hgap⟩ := (hodd 2 (by decide)).2.2 parity 2 (by decide)
  have heq : (x 0 : ℕ) % 2 = (x 1 : ℕ) % 2 := congrArg Fin.val (hx 0 1)
  change d % 2 = 1 at hd
  simp [hgap] at heq
  omega

end MetaMathlibExt.large_union_partition

namespace MetaMathlibExt.coloring_avoids_diffsequence_of_fractional_bounds

-- Odd gaps attain both fractional-part bounds and the forbidden length is exactly two.
example : ∃ c : ℕ+ → Fin 2, ¬ ∃ x : Fin 2 → ℕ+,
    IsMonochromatic c x ∧
      IsDDiffSequence (Set.range fun n : ℕ => 2 * n + 1) (fun i => ((x i : ℕ) : ℤ)) := by
  let d (n : ℕ) := 2 * n + 1
  have hfrac (n : ℕ) : Int.fract ((1 / 2 : ℝ) * (d n : ℝ)) = 1 / 2 := by
    have heq : (1 / 2 : ℝ) * (d n : ℝ) = 1 / 2 + n := by
      simp only [d, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    rw [heq, Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  have h := coloring_avoids_diffsequence_of_fractional_bounds 2 (by decide) _ d
    (fun i j hij => by dsimp [d]; omega) rfl (by decide) (1 / 2) (1 / 2) (by norm_num)
    (fun n => by rw [hfrac]; norm_num)
  have hlen : Nat.ceil ((((2 : ℕ) : ℝ) * (1 / 2 : ℝ))⁻¹) = 1 := by norm_num
  rw [hlen] at h
  exact h

end MetaMathlibExt.coloring_avoids_diffsequence_of_fractional_bounds
