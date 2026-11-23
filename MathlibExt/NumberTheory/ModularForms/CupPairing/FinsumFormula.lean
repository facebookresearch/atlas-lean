/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum.lean`
and
`P2M/Sol/S_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum.lean`
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

public import MathlibExt.NumberTheory.ModularForms.CupPairing.Defs
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import MathlibExt.NumberTheory.ModularForms.CupPairing.CuspSum
import MathlibExt.NumberTheory.ModularForms.ModularGroupSerreTree
import Mathlib.Tactic.FieldSimp

/-!
# A coset-sum formula for the cup pairing

For parabolic homomorphisms `x y : Additive Γ →+ ℤ`, `mult Γ * pair Γ x y` equals minus a finite
sum over `SL(2, ℤ) ⧸ Γ` built from a `T`-invariant primitive of `x` and an `S`- and
`S * T`-invariant decomposition of a primitive of `y`.
-/

set_option linter.unusedSectionVars false

namespace ModularCurve
namespace CupPairing
namespace Compare
open ModularCurve.CupPairing ModularCurve

open Matrix.SpecialLinearGroup ModularGroup MulAction ModularCurve.PDPairing ModularCurve.Period

open scoped MatrixGroups

private theorem S_mul_S : S * S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem U_cube : S * T * (S * T) * (S * T) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem S_mul_U : S * (S * T) = -T := by
  rw [← mul_assoc, S_mul_S, neg_one_mul]

private theorem neg_eq_S_mul_S_mul (g : SL(2, ℤ)) : -g = S * (S * g) := by
  rw [← mul_assoc, S_mul_S, neg_one_mul]

private theorem T_mul_eq (g : SL(2, ℤ)) : T * g = -(S * (S * T * g)) := by
  rw [← mul_assoc S, S_mul_U, neg_mul, neg_neg]

private theorem U_mul_T_pow (g : SL(2, ℤ)) (j : ℕ) : S * T * (T ^ j * g) = S * (T ^ (j + 1) * g) :=
    by
  rw [pow_succ']; group

section Invariant

variable {X : Sort*}

private theorem apply_mul_eq_of_invariant (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g)
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

private theorem T_invariant_of_S_U (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g)
    (hU : ∀ g, F (S * T * g) = F g) (g : SL(2, ℤ)) : F (T * g) = F g := by
  have := hS (T * g)
  rw [← mul_assoc] at this
  rw [← this, hU]

private theorem neg_invariant_of_S (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g) (g : SL(2, ℤ)) :
    F (-g) = F g := by
  rw [neg_eq_S_mul_S_mul, hS, hS]

private theorem eq_apply_one_of_S_U (F : SL(2, ℤ) → X) (hS : ∀ g, F (S * g) = F g)
    (hU : ∀ g, F (S * T * g) = F g) (g : SL(2, ℤ)) : F g = F 1 := by
  have := apply_mul_eq_of_invariant F hS (T_invariant_of_S_U F hS hU) g 1
  rwa [mul_one] at this

end Invariant

section OrbitSums

variable {G : Type*} [Group G] (H : Subgroup G) (t : G)
variable {M : Type*} [AddCommGroup M]

private theorem sum_zmod_cast (n : ℕ) [NeZero n] (f : ℤ → M) :
    ∑ k : ZMod n, f (ZMod.cast k) = ∑ j ∈ Finset.range n, f j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [← Fin.sum_univ_eq_sum_range (fun j => f j)]
  rfl

private theorem pow_minimalPeriod_smul (q₀ : G ⧸ H) :
    t ^ Function.minimalPeriod (t • ·) q₀ • q₀ = q₀ :=
  pow_smul_eq_iff_minimalPeriod_dvd.mpr (dvd_refl _)

variable [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))]

private theorem sum_eq_sum_orbits (F : G ⧸ H → M) :
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
private theorem minimalPeriod_pow_smul (q₀ : G ⧸ H) (j : ℕ) [Finite (G ⧸ H)] :
    Function.minimalPeriod (t • ·) (t ^ j • q₀) = Function.minimalPeriod (t • ·) q₀ := by
  have hper : q₀ ∈ Function.periodicPts (t • ·) :=
    Function.minimalPeriod_pos_iff_mem_periodicPts.mp (NeZero.pos _)
  have := Function.minimalPeriod_apply_iterate hper j
  rwa [smul_iterate] at this

omit [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))] in
private theorem sum_period_shift_one (q₀ : G ⧸ H) (F : G ⧸ H → M) :
    ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) q₀), F (t ^ (k + 1) • q₀) =
      ∑ k ∈ Finset.range (Function.minimalPeriod (t • ·) q₀), F (t ^ k • q₀) := by
  set w := Function.minimalPeriod (t • ·) q₀ with hw
  have h := Finset.sum_range_succ (fun k => F (t ^ k • q₀)) w
  have h' := Finset.sum_range_succ' (fun k => F (t ^ k • q₀)) w
  rw [h', pow_minimalPeriod_smul, pow_zero, one_smul] at h
  exact add_right_cancel h

omit [Fintype (G ⧸ H)] [Fintype (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸ H))] in
private theorem sum_period_shift (q₀ : G ⧸ H) (F : G ⧸ H → M) (j : ℕ) [Finite (G ⧸ H)] :
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
private theorem exists_out_eq_pow_smul (q₀ : G ⧸ H) [Finite (G ⧸ H)] :
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

private theorem sum_range_mul_of_periodic (F : ℕ → M) (w : ℕ) (hF : ∀ k, F (k + w) = F k) (m : ℕ) :
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

private theorem sum_mul_indicator_class [DecidableEq (orbitRel.Quotient (Subgroup.zpowers t) (G ⧸
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

section Main

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
variable (x y : Additive Γ →+ ℤ) (hx : IsParabolicHom Γ x) (hy : IsParabolicHom Γ y)
variable (F : SL(2, ℤ) → ℤ) (hFT : ∀ g, F (T * g) = F g) (hFneg : ∀ g, F (-g) = F g)
variable (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
variable (a b : SL(2, ℤ) → ℤ) (ha : ∀ g, a (S * g) = a g) (hb : ∀ g, b (S * T * g) = b g)
variable (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
variable (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ))

private def cc (g : SL(2, ℤ)) : ℤ := F g * (b g - a g)

include ha hb in
private theorem d_neg (g : SL(2, ℤ)) : b (-g) - a (-g) = b g - a g := by
  rw [neg_invariant_of_S a ha]
  have h3 : -g = S * T * (S * T * (S * T * g)) := by
    rw [← mul_assoc, ← mul_assoc, U_cube, neg_one_mul]
  rw [h3, hb, hb, hb]

include ha hb hFneg in
private theorem cc_neg (g : SL(2, ℤ)) : cc F a b (-g) = cc F a b g := by
  unfold cc; rw [hFneg, d_neg a b ha hb]

include hay hby in
private theorem d_mul (g : SL(2, ℤ)) (γ : Γ) : b (g * γ) - a (g * γ) = b g - a g := by
  rw [hay, hby]; ring

private structure Pot where
  Qa : SL(2, ℤ) → ℤ
  Qb : SL(2, ℤ) → ℤ
  hQa : ∀ g, Qa (S * g) = Qa g
  hQb : ∀ g, Qb (S * T * g) = Qb g
  hQ : ∀ g, cc F a b g = Qb g - Qa g

include ha hb hFneg in
private theorem nonempty_pot : Nonempty (Pot F a b) := by
  obtain ⟨Qa, Qb, h1, h2, h3⟩ :=
    ModularGroup.exists_apply_eq_sub_of_apply_neg_eq (cc F a b) (cc_neg F hFneg a b ha hb)
  exact ⟨⟨Qa, Qb, h1, h2, h3⟩⟩

variable {F a b} (P : Pot F a b)

private theorem Qa_mul_sub (γ : Γ) (g : SL(2, ℤ))
    (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
    (ha : ∀ g, a (S * g) = a g) (hb : ∀ g, b (S * T * g) = b g)
    (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
    (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ)) :
    P.Qa (g * γ) - P.Qa g - x (Additive.ofMul γ) * a g =
      P.Qa γ - P.Qa 1 - x (Additive.ofMul γ) * a 1 := by
  have key : ∀ h, P.Qa (h * γ) - P.Qa h - x (Additive.ofMul γ) * a h =
      P.Qb (h * γ) - P.Qb h - x (Additive.ofMul γ) * b h := by
    intro h
    have h1 := P.hQ h
    have h2 := P.hQ (h * γ)
    unfold cc at h1 h2
    rw [hFx, d_mul y a b hay hby] at h2
    nlinarith [h1, h2]
  have := eq_apply_one_of_S_U (fun h => P.Qa (h * γ) - P.Qa h - x (Additive.ofMul γ) * a h)
    (fun h => by simp only [mul_assoc, P.hQa, ha])
    (fun h => by
      show P.Qa (S * T * h * γ) - P.Qa (S * T * h) - x (Additive.ofMul γ) * a (S * T * h) =
        P.Qa (h * γ) - P.Qa h - x (Additive.ofMul γ) * a h
      rw [key, key, mul_assoc (S * T) h γ, P.hQb, P.hQb, hb]) g
  simpa using this

private def h1 (γ : Γ) : ℤ := P.Qa γ - P.Qa 1

private theorem h1_mul (γ γ' : Γ)
    (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
    (ha : ∀ g, a (S * g) = a g) (hb : ∀ g, b (S * T * g) = b g)
    (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
    (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ)) :
    h1 P (γ * γ') = h1 P γ + h1 P γ' + x (Additive.ofMul γ') * y (Additive.ofMul γ) := by
  unfold h1
  have h := Qa_mul_sub x y P γ' (γ : SL(2, ℤ)) hFx ha hb hay hby
  have hyγ : a γ - a 1 = y (Additive.ofMul γ) := by
    have := hay 1 γ; rw [one_mul] at this; linarith
  have h2 : x (Additive.ofMul γ') * a γ - x (Additive.ofMul γ') * a 1 =
      x (Additive.ofMul γ') * y (Additive.ofMul γ) := by rw [← mul_sub, hyγ]
  rw [Subgroup.coe_mul]
  linarith

private def hq (γ : Γ) : ℚ := ((2 * h1 P γ - x (Additive.ofMul γ) * y (Additive.ofMul γ) : ℤ) : ℚ)

private theorem isPrimitive_hq
    (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
    (ha : ∀ g, a (S * g) = a g) (hb : ∀ g, b (S * T * g) = b g)
    (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
    (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ)) :
    IsPrimitive ((Int.castAddHom ℚ).comp x) ((Int.castAddHom ℚ).comp y) (hq x y P) := by
  intro g g'
  unfold hq
  simp only [omega, AddMonoidHom.coe_comp, Function.comp_apply, Int.coe_castAddHom, ofMul_mul,
    map_add, h1_mul x y P g g' hFx ha hb hay hby]
  push_cast
  ring

private theorem Qa_T_mul_sub (m : SL(2, ℤ)) : P.Qa (T * m) - P.Qa m = cc F a b m - cc F a b (S * (T
    * m)) := by
  have hT : P.Qa (T * m) = P.Qa (S * T * m) := by
    conv_lhs => rw [T_mul_eq, neg_invariant_of_S P.Qa P.hQa, P.hQa]
  have e1 := P.hQ m
  have e2 := P.hQ (S * T * m)
  rw [P.hQb, mul_assoc] at e2
  rw [hT, mul_assoc]
  linarith

private theorem Qa_T_pow_mul_sub (g : SL(2, ℤ)) (n : ℕ) :
    P.Qa (T ^ n * g) - P.Qa g =
      ∑ k ∈ Finset.range n, (cc F a b (T ^ k * g) - cc F a b (S * (T ^ (k + 1) * g))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have step := Qa_T_mul_sub P (T ^ n * g)
    rw [← mul_assoc, ← pow_succ'] at step
    linarith

private theorem a_T_pow_mul_sub (ha : ∀ g, a (S * g) = a g) (hb : ∀ g, b (S * T * g) = b g)
    (g : SL(2, ℤ)) (n : ℕ) :
    a (T ^ n * g) - a g =
      ∑ k ∈ Finset.range n, ((b (T ^ k * g) - a (T ^ k * g)) -
        (b (S * (T ^ (k + 1) * g)) - a (S * (T ^ (k + 1) * g)))) := by
  have step1 : ∀ m, a (T * m) - a m = (b m - a m) - (b (S * (T * m)) - a (S * (T * m))) := by
    intro m
    have hT : a (T * m) = a (S * T * m) := by
      conv_lhs => rw [T_mul_eq, neg_invariant_of_S a ha, ha]
    rw [hT, ← mul_assoc S T m, hb]
    ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have step := step1 (T ^ n * g)
    rw [← mul_assoc, ← pow_succ'] at step
    linarith

end Main

section Eval

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
variable (x y : Additive Γ →+ ℤ) (hx : IsParabolicHom Γ x) (hy : IsParabolicHom Γ y)
variable {F : SL(2, ℤ) → ℤ} (hFT : ∀ g, F (T * g) = F g) (hFneg : ∀ g, F (-g) = F g)
variable (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
variable {a b : SL(2, ℤ) → ℤ} (ha : ∀ g, a (S * g) = a g) (hb : ∀ g, b (S * T * g) = b g)
variable (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
variable (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ))
variable (Φ : SL(2, ℤ) ⧸ Γ → ℤ) (hΦ : ∀ g, Φ (QuotientGroup.mk g) = (F g - F (S * g)) * (b g - a g))
variable (P : Pot F a b)

private theorem trace_conj_T_pow (z : SL(2, ℤ)) (n : ℕ) :
    ((z⁻¹ * T ^ n * z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    ← zpow_natCast, ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  norm_num

include hx hFx ha hb hay hby hy in
private theorem h1_conj (g : SL(2, ℤ)) (w : ℕ) (hmem : g⁻¹ * T ^ w * g ∈ Γ) :
    h1 P ⟨g⁻¹ * T ^ w * g, hmem⟩ = P.Qa (T ^ w * g) - P.Qa g := by
  have hxπ : x (Additive.ofMul (⟨g⁻¹ * T ^ w * g, hmem⟩ : Γ)) = 0 := hx _ (trace_conj_T_pow g w)
  have h := Qa_mul_sub x y P ⟨g⁻¹ * T ^ w * g, hmem⟩ g hFx ha hb hay hby
  rw [hxπ] at h
  simp only [zero_mul, sub_zero] at h
  have hg : g * (g⁻¹ * T ^ w * g) = T ^ w * g := by group
  unfold h1
  rw [← h, hg]

include hy hay ha hb in
private theorem sum_d_eq (g : SL(2, ℤ)) (w : ℕ) (hmem : g⁻¹ * T ^ w * g ∈ Γ) :
    ∑ k ∈ Finset.range w, (b (T ^ k * g) - a (T ^ k * g)) =
      ∑ k ∈ Finset.range w, (b (S * (T ^ (k + 1) * g)) - a (S * (T ^ (k + 1) * g))) := by
  have h := a_T_pow_mul_sub ha hb g w
  have hyπ : y (Additive.ofMul (⟨g⁻¹ * T ^ w * g, hmem⟩ : Γ)) = 0 := hy _ (trace_conj_T_pow g w)
  have h0 : a (T ^ w * g) - a g = 0 := by
    have := hay g ⟨g⁻¹ * T ^ w * g, hmem⟩
    rw [hyπ, add_zero] at this
    rw [← this]
    simp only [sub_eq_zero]
    congr 1; group
  rw [h0, Finset.sum_sub_distrib] at h
  linarith

include hx hy hFT hFneg hFx ha hb hay hby hΦ in
private theorem h1_conj_eq_neg_sum (g : SL(2, ℤ)) (w : ℕ) (hmem : g⁻¹ * T ^ w * g ∈ Γ) :
    h1 P ⟨g⁻¹ * T ^ w * g, hmem⟩ =
      -∑ k ∈ Finset.range w, Φ (S • T ^ (k + 1) • (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ)) := by
  rw [h1_conj x y hx hy hFx ha hb hay hby P g w hmem, Qa_T_pow_mul_sub P g w]
  have hF1 : ∀ k, F (T ^ k * g) = F g := by
    intro k; induction k with
    | zero => rw [pow_zero, one_mul]
    | succ k ih => rw [pow_succ', mul_assoc, hFT, ih]
  have step1 : ∑ k ∈ Finset.range w, (cc F a b (T ^ k * g) - cc F a b (S * (T ^ (k + 1) * g))) =
      ∑ k ∈ Finset.range w, (F (T ^ (k + 1) * g) - F (S * (T ^ (k + 1) * g))) *
        (b (S * (T ^ (k + 1) * g)) - a (S * (T ^ (k + 1) * g))) := by
    unfold cc
    have hsum := sum_d_eq y hy ha hb hay g w hmem
    simp only [hF1]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [step1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  set m := T ^ (k + 1) * g with hm
  have hΦ' : Φ (S • T ^ (k + 1) • (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ)) = (F (S * m) - F (S * (S *
      m))) *
      (b (S * m) - a (S * m)) := by
    rw [← hΦ (S * m)]
    rfl
  rw [hΦ', ← neg_eq_S_mul_S_mul, hFneg]
  ring

include hx hy hFT hFneg hFx ha hb hay hby hΦ in
private theorem h1_cuspGen (c : Cusp Γ) :
    h1 P (cuspGen Γ c) = -∑ k ∈ Finset.range (Function.minimalPeriod (T • ·) c.out),
      Φ (S • T ^ (k + 1) • c.out) := by
  have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem Γ T c.out
  have h := h1_conj_eq_neg_sum x y hx hy hFT hFneg hFx ha hb hay hby Φ hΦ P c.out.out
    (Function.minimalPeriod (T • ·) c.out) hmem
  rw [QuotientGroup.out_eq'] at h
  exact h

include hx hy hFT hFneg hFx ha hb hay hby hΦ in
private theorem sum_h1_cuspGen [Fintype (SL(2, ℤ) ⧸ Γ)] :
    ∑ c : Cusp Γ, h1 P (cuspGen Γ c) = -∑ q, Φ q := by
  classical
  have hS : ∑ q, Φ q = ∑ q, Φ (S • q) :=
    (Fintype.sum_equiv (MulAction.toPerm (S : SL(2, ℤ))) (fun q => Φ (S • q)) Φ (fun _ => rfl)).symm
  rw [hS, sum_eq_sum_orbits Γ T (fun q => Φ (S • q)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h1_cuspGen x y hx hy hFT hFneg hFx ha hb hay hby Φ hΦ P c]
  rw [sum_period_shift_one Γ T c.out (fun q => Φ (S • q))]

include hx hy hFT hFneg hFx ha hb hay hby hΦ P in
private theorem main : (mult Γ : ℚ) * pair Γ ((Int.castAddHom ℚ).comp x) ((Int.castAddHom ℚ).comp
    y) =
    -((∑ᶠ q, Φ q : ℤ) : ℚ) := by
  classical
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  rw [ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive Γ _ _ (hq x y P)
    (isPrimitive_hq x y P hFx ha hb hay hby)]
  have hcs : cuspSum Γ (hq x y P) = 2 * ((∑ c : Cusp Γ, h1 P (cuspGen Γ c) : ℤ) : ℚ) := by
    unfold cuspSum hq
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hxπ : x (Additive.ofMul (cuspGen Γ c)) = 0 := by
      apply hx
      have := trace_conj_T_pow c.out.out (Function.minimalPeriod (T • ·) c.out)
      exact this
    rw [hxπ]
    push_cast
    ring
  rw [hcs, sum_h1_cuspGen x y hx hy hFT hFneg hFx ha hb hay hby Φ hΦ P, finsum_eq_sum_of_fintype]
  have := mult_ne_zero Γ
  field_simp
  push_cast
  ring

end Eval

end ModularCurve.CupPairing.Compare

open scoped MatrixGroups in
open ModularCurve.CupPairing.Compare in
/-- A coset-sum formula for the cup pairing of two parabolic homomorphisms `x y`, in terms of a
`T`-invariant primitive `F` of `x` and primitives `a`, `b` of `y` invariant under `S` and
`S * T`. -/
public theorem ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex]
    (x y : Additive Γ →+ ℤ) (hx : ModularCurve.Period.IsParabolicHom Γ x)
    (hy : ModularCurve.Period.IsParabolicHom Γ y)
    (F : SL(2, ℤ) → ℤ) (hFT : ∀ g, F (ModularGroup.T * g) = F g) (hFneg : ∀ g, F (-g) = F g)
    (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
    (a b : SL(2, ℤ) → ℤ) (ha : ∀ g, a (ModularGroup.S * g) = a g)
    (hb : ∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g)
    (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
    (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ))
    (Φ : SL(2, ℤ) ⧸ Γ → ℤ)
    (hΦ : ∀ g, Φ (QuotientGroup.mk g) = (F g - F (ModularGroup.S * g)) * (b g - a g)) :
    (ModularCurve.CupPairing.mult Γ : ℚ) *
        ModularCurve.CupPairing.pair Γ ((Int.castAddHom ℚ).comp x) ((Int.castAddHom ℚ).comp y) =
      -((∑ᶠ q, Φ q : ℤ) : ℚ) := by
  obtain ⟨P⟩ := nonempty_pot F hFneg a b ha hb
  exact main x y hx hy hFT hFneg hFx ha hb hay hby Φ hΦ P
