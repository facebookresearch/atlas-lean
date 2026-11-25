/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.NagellLjunggrenCubeNoSolution
import MathlibExt.NumberTheory.SqAddAddOneEqThreeMulCube

/-!
# Integer solutions of $u^3 - 2v^3 = 1$

The equation has exactly the solutions $(1,0)$ and $(-1,-1)$. Reduction modulo nine
separates the case $3 ∣ v$, where coprime factors of a cube are cubes, from the case
$u ≡ v ≡ -1$ modulo three, where the cubic-unit uniqueness lemma applies.
-/

namespace MetaMathlibExt

namespace cube_sub_two_mul_cube_eq_one_iff

/-- When `3 ∣ v`, we have `u = 18t + 1`. The equation then expresses a cube as
the product of `t` and the coprime factor `(u² + u + 1) / 3`. -/
private theorem of_three_dvd {u v : ℤ} (h : u ^ 3 - 2 * v ^ 3 = 1) (hv : 3 ∣ v) :
    (u, v) = (1, 0) := by
  obtain ⟨s, rfl⟩ := hv
  have hc : u ^ 3 = 1 + 54 * s ^ 3 := by linear_combination h
  have hc' := congrArg (fun z : ℤ => (z : ZMod 54)) hc
  push_cast at hc'
  let reduce := ZMod.castHom (by decide : 18 ∣ 54) (ZMod 18)
  have table : ∀ x : ZMod 54, x ^ 3 = 1 → reduce x = 1 := by decide
  have hu : (u : ZMod 18) = 1 := by
    simpa only [reduce, map_intCast] using table u (by
      simpa [show (54 : ZMod 54) = 0 from rfl] using hc')
  obtain ⟨t, ht⟩ : (18 : ℤ) ∣ u - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    simp [hu]
  have hu' : u = 18 * t + 1 := by omega
  let f := 108 * t ^ 2 + 18 * t + 1
  have hprod : f * t = s ^ 3 := by
    rw [hu'] at hc
    dsimp [f]
    linarith only [hc]
  have hcop : IsCoprime f t := ⟨1, -(108 * t + 18), by dsimp [f]; ring⟩
  obtain ⟨w, hw⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop (by decide : Odd 3) hprod
  have hquad : u ^ 2 + u + 1 = 3 * w ^ 3 := by rw [hu', ← hw]; dsimp [f]; ring
  have hcases := (sq_add_add_one_eq_three_mul_cube_iff u w).1.mp hquad
  simp only [Prod.mk.injEq] at hcases
  have hu1 : u = 1 := by omega
  have hs : s = 0 := by simpa [hu1] using hc
  simp [hu1, hs]

end cube_sub_two_mul_cube_eq_one_iff

/-- **Integer solutions of $u^3 - 2v^3 = 1$.** For all integers $u$ and $v$, $u^3 - 2v^3 = 1$ if
and only if $(u, v) = (1, 0)$ or $(u, v) = (-1, -1)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 7
(`integers-2025-A103-lem-7`). -/
public theorem cube_sub_two_mul_cube_eq_one_iff (u v : ℤ) :
    u ^ 3 - 2 * v ^ 3 = 1 ↔ (u, v) = (1, 0) ∨ (u, v) = (-1, -1) := by
  constructor
  · intro h
    let reduce := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)
    have table : ∀ x y : ZMod 9, x ^ 3 - 2 * y ^ 3 = 1 →
        reduce y = 0 ∨ (reduce y = -1 ∧ reduce x = -1) := by decide
    have hmod := congrArg (fun z : ℤ => (z : ZMod 9)) h
    push_cast at hmod
    have cases := table u v hmod
    simp only [reduce, map_intCast] at cases
    rcases cases with hv | ⟨hv, hu⟩
    · exact Or.inl (cube_sub_two_mul_cube_eq_one_iff.of_three_dvd h
        ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hv))
    · have heq := NagellLjunggren.eq_of_succ_mul_cube_sub_mul_cube_eq_one
          (a := 2) (b := 1) (U := -v) (V := -u) (by decide) (by decide)
          (by linear_combination h) (by simp [hv]) (by simp [hu])
      have huv : u = v := by omega
      subst v
      have hc : u ^ 3 = (-1 : ℤ) ^ 3 := by linear_combination -h
      have hu1 := (by decide : Odd 3).pow_injective hc
      exact Or.inr (by rw [hu1])
  · rintro (h | h) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> decide

end MetaMathlibExt
