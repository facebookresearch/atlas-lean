/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`P2M/Sol/S_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum.lean`,
`P2M/Sol/S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean`
and
`P2M/Sol/S_ModularCurve_CupPairing_exists_perfectPairing_intCast_eq_pair.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Orbit sums and `S`, `T` relations for the cup pairing

Support lemmas shared by the cup pairing files:

* relations between `S`, `T` and `S * T` in `SL(2, ℤ)`, and the fact that a function on `SL(2, ℤ)`
  invariant under left multiplication by `S` and by `S * T` is constant;
* sums over `G ⧸ H` regrouped along the orbits of `⟨t⟩`, and sums along a single orbit.
-/

public section

namespace ModularCurve.CupPairing.OrbitSum

open Matrix.SpecialLinearGroup ModularGroup MulAction

open scoped MatrixGroups

theorem U_cube : S * T * (S * T) * (S * T) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem S_mul_U : S * (S * T) = -T := by
  rw [← mul_assoc, S_mul_S_eq, neg_one_mul]

theorem neg_eq_S_mul_S_mul (g : SL(2, ℤ)) : -g = S * (S * g) := by
  rw [← mul_assoc, S_mul_S_eq, neg_one_mul]

theorem T_mul_eq (g : SL(2, ℤ)) : T * g = -(S * (S * T * g)) := by
  rw [← mul_assoc S, S_mul_U, neg_mul, neg_neg]

theorem U_mul_T_pow (g : SL(2, ℤ)) (j : ℕ) : S * T * (T ^ j * g) = S * (T ^ (j + 1) * g) :=
    by
  rw [pow_succ']; group

section Invariant

variable {X : Sort*}

theorem apply_mul_eq_of_invariant (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g)
    (hT : ∀ g, F (T * g) = F g) (h g : SL(2, ℤ)) : F (h * g) = F g := by
  have hmem : h ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hmem using Subgroup.closure_induction generalizing g with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hS g
    · exact hT g
  | one => rw [one_mul]
  | mul x y _ _ ihx ihy => rw [mul_assoc, ihx, ihy]
  | inv x _ ih =>
    have := ih (x⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    exact this.symm

theorem T_invariant_of_S_U (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g)
    (hU : ∀ g, F (S * T * g) = F g) (g : SL(2, ℤ)) : F (T * g) = F g := by
  have := hS (T * g)
  rw [← mul_assoc] at this
  rw [← this, hU]

theorem neg_invariant_of_S (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g) (g : SL(2, ℤ)) :
    F (-g) = F g := by
  rw [neg_eq_S_mul_S_mul, hS, hS]

theorem eq_apply_one_of_S_U (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g)
    (hU : ∀ g, F (S * T * g) = F g) (g : SL(2, ℤ)) : F g = F 1 := by
  have := apply_mul_eq_of_invariant F hS (T_invariant_of_S_U F hS hU) g 1
  rwa [mul_one] at this

end Invariant

section OrbitSums

variable {G : Type*} [Group G] (H : Subgroup G) (t : G)
variable {M : Type*} [AddCommGroup M]

theorem sum_zmod_cast (n : ℕ) [NeZero n] (f : ℤ → M) :
    ∑ k : ZMod n, f (ZMod.cast k) = ∑ j ∈ Finset.range n, f j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [← Fin.sum_univ_eq_sum_range (fun j => f j)]
  rfl

theorem pow_minimalPeriod_smul (q₀ : G ⧸ H) :
    t ^ Function.minimalPeriod (t • ·) q₀ • q₀ = q₀ :=
  pow_smul_eq_iff_minimalPeriod_dvd.mpr (dvd_refl _)

variable [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))]

theorem sum_eq_sum_orbits (F : G ⧸ H → M) :
    ∑ x, F x = ∑ c : orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H),
      ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) c.out), F (t ^ k • c.out) := by
  classical
  rw [← Fintype.sum_equiv (H.quotientEquivSigmaZMod t).symm (fun p => F ((H.quotientEquivSigmaZMod
      t).symm p))
    F (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hz : ∀ k : ℕ, F (t ^ k • c.out) = F (t ^ (k : ℤ) • c.out) := fun k => by rw [zpow_natCast]
  simp_rw [hz]
  rw [← sum_zmod_cast _ (fun k : ℤ => F (t ^ k • c.out))]
  rfl

omit [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))] in
theorem minimalPeriod_pow_smul (q₀ : G ⧸ H) (j : ℕ) [Finite (G ⧸ H)] :
    Function.minimalPeriod (t • ·) (t ^ j • q₀) = Function.minimalPeriod (t • ·) q₀ := by
  have hper : q₀ ∈ Function.periodicPts (t • ·) :=
    Function.minimalPeriod_pos_iff_mem_periodicPts.mp (NeZero.pos _)
  have := Function.minimalPeriod_apply_iterate hper j
  rwa [smul_iterate] at this

omit [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))] in
theorem sum_period_shift_one (q₀ : G ⧸ H) (F : G ⧸ H → M) :
    ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) q₀), F (t ^ (k + 1) • q₀) =
      ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) q₀), F (t ^ k • q₀) := by
  set w := Function.minimalPeriod (t • ·) q₀ with hw
  have h := Finset.sum_range_succ (fun k => F (t ^ k • q₀)) w
  have h' := Finset.sum_range_succ' (fun k => F (t ^ k • q₀)) w
  rw [h', pow_minimalPeriod_smul, pow_zero, one_smul] at h
  exact add_right_cancel h

omit [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))] in
theorem sum_period_shift (q₀ : G ⧸ H) (F : G ⧸ H → M) (j : ℕ) [Finite (G ⧸ H)] :
    ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) (t ^ j • q₀)), F (t ^ k • (t ^ j • q₀)) =
      ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) q₀), F (t ^ k • q₀) := by
  rw [minimalPeriod_pow_smul]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have h1 := sum_period_shift_one H t (t ^ j • q₀) F
    rw [minimalPeriod_pow_smul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add, show k + (j + 1) = k + 1 + j by omega]

omit [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))] in
theorem exists_out_eq_pow_smul (q₀ : G ⧸ H) [Finite (G ⧸ H)] :
    ∃ j : ℕ, (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) q₀ :
      orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H)).out = t ^ j • q₀ := by
  have hmem : (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) q₀ :
      orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H)).out ∈ orbit (Subgroup.zpowers t) q₀ :=
    orbitRel_apply.mp (Quotient.exact (Quotient.out_eq _))
  obtain ⟨⟨z, hz⟩, hzq⟩ := mem_orbit_iff.mp hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨(i % (Function.minimalPeriod (t • ·) q₀ : ℤ)).toNat, ?_⟩
  rw [← hzq]
  change t ^ i • q₀ = _
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (NeZero.ne _))),
    zpow_smul_mod_minimalPeriod]

theorem sum_range_mul_of_periodic (F : ℕ → M) (w : ℕ) (hF : ∀ k, F (k + w) = F k) (m : ℕ) :
    ∑ k ∈ Finset.range (w * m), F k = m • ∑ k ∈ Finset.range w, F k := by
  have hper : ∀ m k, F (w * m + k) = F k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro k
      rw [Nat.mul_succ, show w * m + w + k = w * m + (k + w) by ring, ih, hF]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hper m k

theorem sum_mul_indicator_class [DecidableEq (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸
    H))]
    (F : G ⧸ H → M) (q₀ : G ⧸ H) :
    ∑ x, (if (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) x :
        orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H)) =
        Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) q₀ then F x else 0) =
      ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) q₀), F (t ^ k • q₀) := by
  classical
  rw [sum_eq_sum_orbits H t]
  rw [Finset.sum_eq_single (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) q₀)]
  · obtain ⟨j, hj⟩ := exists_out_eq_pow_smul H t q₀
    rw [hj, ← sum_period_shift H t q₀ F j]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ite_eq_left]
    apply Quotient.sound
    refine ⟨⟨t ^ (k + j), Subgroup.npow_mem_zpowers t (k + j)⟩, ?_⟩
    change t ^ (k + j) • q₀ = _
    rw [pow_add, mul_smul]
  · intro c _ hc
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right]
    intro h
    apply hc
    rw [← h]
    have hc' : (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) (t ^ k • c.out) :
        orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H)) = Quotient.mk _ c.out :=
      Quotient.sound ⟨⟨t ^ k, Subgroup.npow_mem_zpowers t k⟩, rfl⟩
    rw [hc', Quotient.out_eq]
  · intro h; exact absurd (Finset.mem_univ _) h

end OrbitSums

end ModularCurve.CupPairing.OrbitSum
