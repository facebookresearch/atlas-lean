/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.GroupTheory.Subgroup.Saturated

/-!
# Power root closure of an actual commutative submonoid

The carrier is {x | some positive power of x lies in S}. This is the fs
root closure used in log geometry; the localization notion MulSaturated
has a different defining condition. References: Kato §1;
Gross--Siebert arXiv:1102.4322v2, Construction1.16.
-/

@[expose] public section
namespace Submonoid
variable {M : Type*} [CommMonoid M]

/-- The actual positive-power root closure. -/
def powerRootClosure (S : Submonoid M) : Submonoid M where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ x^n ∈ S}
  one_mem' := ⟨1, by decide, by simp⟩
  mul_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n*m, Nat.mul_pos hn hm, ?_⟩
    have he : (x*y)^(n*m) = (x^n)^m * (y^m)^n := by
      rw [mul_pow]
      congr 1
      · exact pow_mul x n m
      · rw [Nat.mul_comm n m, pow_mul]
    rw [he]
    exact S.mul_mem (S.pow_mem hx m) (S.pow_mem hy n)

@[simp] theorem mem_powerRootClosure (S : Submonoid M) (x : M) :
    x ∈ S.powerRootClosure ↔ ∃ n : ℕ, 0 < n ∧ x^n ∈ S := Iff.rfl

theorem le_powerRootClosure (S : Submonoid M) : S ≤ S.powerRootClosure :=
  fun _x hx => ⟨1, by decide, by simpa using hx⟩

theorem powerRootClosure_mono {S T : Submonoid M} (h : S ≤ T) :
    S.powerRootClosure ≤ T.powerRootClosure := by
  rintro x ⟨n, hn, hx⟩
  exact ⟨n, hn, h hx⟩

theorem powerRootClosure_powSaturated (S : Submonoid M) :
    S.powerRootClosure.PowSaturated := by
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  · obtain ⟨m, hm, hxm⟩ := hx
    exact Or.inr ⟨n*m, Nat.mul_pos (Nat.pos_of_ne_zero hn) hm, by
      simpa only [pow_mul] using hxm⟩

end Submonoid
