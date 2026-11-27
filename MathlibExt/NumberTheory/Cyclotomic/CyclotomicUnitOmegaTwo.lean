/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero.lean` and
`P2M/Sol/S_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.UnitsModPowersEigenspace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# The `ω²` component of the cyclotomic unit `1 + ζ_p`

For a prime `p ≥ 5`, `Stickelberger.omegaIdempotent_two_cycloUnitTwo_ne_zero` shows that the
projector `Stickelberger.omegaIdempotent` with `i = 2` does not kill the class of the unit
`1 + ζ_p` in `E / E ^ p`, where `E = 𝓞 (ℚ(ζ_p))ˣ`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Graduate Texts in Mathematics
  83, Springer, 1997, Chapters 8 and 15.
* F. Thaine, *On the ideal class groups of real abelian number fields*, Ann. of Math. (2) 128
  (1988), 1–18.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial NumberField

namespace Aux1B2

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev S : Type := AdjoinRoot ((X : (ZMod p)[X]) ^ 3)

private lemma monic_X3 : ((X : (ZMod p)[X]) ^ 3).Monic := monic_X_pow 3

private noncomputable def eps : S p := AdjoinRoot.root _

private lemma eps_pow_three : (eps p) ^ 3 = 0 := by
  rw [eps, ← AdjoinRoot.mk_X, ← map_pow]
  exact AdjoinRoot.mk_self

private noncomputable def co (k : ℕ) : S p →ₗ[ZMod p] ZMod p :=
  (Polynomial.lcoeff (ZMod p) k).comp (AdjoinRoot.modByMonicHom (monic_X3 p))

private lemma co_mk (k : ℕ) (hk : k < 3) (f : (ZMod p)[X]) :
    co p k (AdjoinRoot.mk _ f) = f.coeff k := by
  simp only [co, LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk, Polynomial.lcoeff_apply]
  conv_rhs => rw [← Polynomial.modByMonic_add_div f ((X : (ZMod p)[X]) ^ 3)]
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

private lemma co_mul (x y : S p) :
    co p 0 (x * y) = co p 0 x * co p 0 y ∧
    co p 1 (x * y) = co p 0 x * co p 1 y + co p 1 x * co p 0 y ∧
    co p 2 (x * y) = co p 0 x * co p 2 y + co p 1 x * co p 1 y + co p 2 x * co p 0 y := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [← map_mul]
  simp only [co_mk p 0 (by norm_num), co_mk p 1 (by norm_num), co_mk p 2 (by norm_num),
    Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero]
  refine ⟨by simp, by simp, by simp⟩

private lemma co_one : co p 0 1 = 1 ∧ co p 1 1 = 0 ∧ co p 2 1 = 0 := by
  rw [← map_one (AdjoinRoot.mk ((X : (ZMod p)[X]) ^ 3)), ← Polynomial.C_1]
  simp only [co_mk p 0 (by norm_num), co_mk p 1 (by norm_num), co_mk p 2 (by norm_num),
    Polynomial.coeff_C]
  simp

private lemma co_eps : co p 0 (eps p) = 0 ∧ co p 1 (eps p) = 1 ∧ co p 2 (eps p) = 0 := by
  rw [eps, ← AdjoinRoot.mk_X]
  simp only [co_mk p 0 (by norm_num), co_mk p 1 (by norm_num), co_mk p 2 (by norm_num),
    Polynomial.coeff_X]
  simp

private lemma co_one_add_eps_pow (hp2 : p ≠ 2) (n : ℕ) :
    co p 0 ((1 + eps p) ^ n) = 1 ∧ co p 1 ((1 + eps p) ^ n) = n ∧
    co p 2 ((1 + eps p) ^ n) = ((n : ZMod p) ^ 2 - n) / 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    refine ⟨(co_one p).1, (co_one p).2.1, ?_⟩
    rw [(co_one p).2.2]; ring
  | succ n ih =>
    obtain ⟨h0, h1, h2'⟩ := ih
    obtain ⟨m0, m1, m2⟩ := co_mul p ((1 + eps p) ^ n) (1 + eps p)
    have e0 : co p 0 (1 + eps p) = 1 := by rw [map_add, (co_one p).1, (co_eps p).1]; ring
    have e1 : co p 1 (1 + eps p) = 1 := by rw [map_add, (co_one p).2.1, (co_eps p).2.1]; ring
    have e2 : co p 2 (1 + eps p) = 0 := by rw [map_add, (co_one p).2.2, (co_eps p).2.2]; ring
    rw [pow_succ (1 + eps p) n, m0, m1, m2, h0, h1, h2', e0, e1, e2]
    refine ⟨by ring, by push_cast; ring, ?_⟩
    push_cast
    field_simp
    ring

private noncomputable def ψ (x : S p) : ZMod p :=
  co p 1 x / co p 0 x + 2 * (co p 2 x / co p 0 x) - (co p 1 x / co p 0 x) ^ 2

private lemma ψ_mul (x y : S p) (hx : co p 0 x ≠ 0) (hy : co p 0 y ≠ 0) :
    ψ p (x * y) = ψ p x + ψ p y := by
  obtain ⟨m0, m1, m2⟩ := co_mul p x y
  simp only [ψ, m0, m1, m2]
  field_simp
  ring

private lemma natDegree_modByMonicHom_lt (z : S p) :
    (AdjoinRoot.modByMonicHom (monic_X3 p) z).degree < 3 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [AdjoinRoot.modByMonicHom_mk]
  have := Polynomial.degree_modByMonic_lt f (monic_X3 p)
  rwa [Polynomial.degree_X_pow] at this

private lemma ext_co (x y : S p) (h0 : co p 0 x = co p 0 y) (h1 : co p 1 x = co p 1 y)
    (h2 : co p 2 x = co p 2 y) : x = y := by
  have hpoly : AdjoinRoot.modByMonicHom (monic_X3 p) x =
      AdjoinRoot.modByMonicHom (monic_X3 p) y := by
    ext k
    by_cases hk : k < 3
    · change co p k x = co p k y
      interval_cases k <;> assumption
    · have hk' : (3 : WithBot ℕ) ≤ k := by exact_mod_cast (not_lt.mp hk)
      rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le (natDegree_modByMonicHom_lt p x) hk'),
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le (natDegree_modByMonicHom_lt p y) hk')]
  calc x = AdjoinRoot.mk _ (AdjoinRoot.modByMonicHom (monic_X3 p) x) :=
        (AdjoinRoot.mk_leftInverse (monic_X3 p) x).symm
    _ = AdjoinRoot.mk _ (AdjoinRoot.modByMonicHom (monic_X3 p) y) := by rw [hpoly]
    _ = y := AdjoinRoot.mk_leftInverse (monic_X3 p) y

private lemma co_of (c : ZMod p) :
    co p 0 (AdjoinRoot.of _ c) = c ∧ co p 1 (AdjoinRoot.of _ c) = 0 ∧
    co p 2 (AdjoinRoot.of _ c) = 0 := by
  rw [← AdjoinRoot.mk_C]
  simp only [co_mk p 0 (by norm_num), co_mk p 1 (by norm_num), co_mk p 2 (by norm_num),
    Polynomial.coeff_C]
  simp

private lemma co_of_mul (c : ZMod p) (x : S p) (k : ℕ) (hk : k < 3) :
    co p k (AdjoinRoot.of _ c * x) = c * co p k x := by
  obtain ⟨m0, m1, m2⟩ := co_mul p (AdjoinRoot.of _ c) x
  obtain ⟨c0, c1, c2⟩ := co_of p c
  interval_cases k
  · rw [m0, c0]
  · rw [m1, c0, c1]; ring
  · rw [m2, c0, c1, c2]; ring

private lemma eq_nf (x : S p) :
    x = AdjoinRoot.of _ (co p 0 x) + AdjoinRoot.of _ (co p 1 x) * eps p +
      AdjoinRoot.of _ (co p 2 x) * eps p ^ 2 := by
  obtain ⟨e0, e1, e2⟩ := co_eps p
  have sq0 : co p 0 (eps p ^ 2) = 0 := by rw [pow_two, (co_mul p _ _).1, e0]; ring
  have sq1 : co p 1 (eps p ^ 2) = 0 := by rw [pow_two, (co_mul p _ _).2.1, e0, e1]; ring
  have sq2 : co p 2 (eps p ^ 2) = 1 := by rw [pow_two, (co_mul p _ _).2.2, e0, e1, e2]; ring
  refine ext_co p _ _ ?_ ?_ ?_
  · rw [map_add, map_add, (co_of p _).1, co_of_mul p _ _ 0 (by norm_num),
      co_of_mul p _ _ 0 (by norm_num), e0, sq0]; ring
  · rw [map_add, map_add, (co_of p _).2.1, co_of_mul p _ _ 1 (by norm_num),
      co_of_mul p _ _ 1 (by norm_num), e1, sq1]; ring
  · rw [map_add, map_add, (co_of p _).2.2, co_of_mul p _ _ 2 (by norm_num),
      co_of_mul p _ _ 2 (by norm_num), e2, sq2]; ring

private noncomputable def τ (n : ℕ) : S p →+* S p :=
  AdjoinRoot.lift (AdjoinRoot.of _) ((1 + eps p) ^ n - 1) (by
    rw [Polynomial.eval₂_X_pow]
    have : (1 + eps p) ^ n - 1 = (∑ i ∈ Finset.range n, (1 + eps p) ^ i) * eps p := by
      rw [← geom_sum_mul, add_sub_cancel_left]
    rw [this, mul_pow, eps_pow_three, mul_zero])

private lemma τ_eps (n : ℕ) : τ p n (eps p) = (1 + eps p) ^ n - 1 := by
  unfold τ eps
  exact AdjoinRoot.lift_root _

private lemma τ_of (n : ℕ) (c : ZMod p) : τ p n (AdjoinRoot.of _ c) = AdjoinRoot.of _ c := by
  unfold τ
  exact AdjoinRoot.lift_of _

private lemma co_τ (hp2 : p ≠ 2) (n : ℕ) (x : S p) :
    co p 0 (τ p n x) = co p 0 x ∧ co p 1 (τ p n x) = co p 1 x * n ∧
    co p 2 (τ p n x) = co p 1 x * (((n : ZMod p) ^ 2 - n) / 2) + co p 2 x * (n : ZMod p) ^ 2 := by
  set y : S p := (1 + eps p) ^ n - 1 with hy
  obtain ⟨p0, p1, p2⟩ := co_one_add_eps_pow p hp2 n
  obtain ⟨o0, o1, o2⟩ := co_one p
  have y0 : co p 0 y = 0 := by rw [hy, map_sub, p0, o0]; ring
  have y1 : co p 1 y = n := by rw [hy, map_sub, p1, o1]; ring
  have y2 : co p 2 y = ((n : ZMod p) ^ 2 - n) / 2 := by rw [hy, map_sub, p2, o2]; ring
  have yy0 : co p 0 (y ^ 2) = 0 := by rw [pow_two, (co_mul p _ _).1, y0]; ring
  have yy1 : co p 1 (y ^ 2) = 0 := by rw [pow_two, (co_mul p _ _).2.1, y0, y1]; ring
  have yy2 : co p 2 (y ^ 2) = (n : ZMod p) ^ 2 := by
    rw [pow_two, (co_mul p _ _).2.2, y0, y1, y2]; ring
  have hτx : τ p n x = AdjoinRoot.of _ (co p 0 x) + AdjoinRoot.of _ (co p 1 x) * y +
      AdjoinRoot.of _ (co p 2 x) * y ^ 2 := by
    conv_lhs => rw [eq_nf p x]
    simp only [map_add, map_mul, map_pow, τ_of, τ_eps, hy]
  rw [hτx]
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add, map_add, (co_of p _).1, co_of_mul p _ _ 0 (by norm_num),
      co_of_mul p _ _ 0 (by norm_num), y0, yy0]; ring
  · rw [map_add, map_add, (co_of p _).2.1, co_of_mul p _ _ 1 (by norm_num),
      co_of_mul p _ _ 1 (by norm_num), y1, yy1]; ring
  · rw [map_add, map_add, (co_of p _).2.2, co_of_mul p _ _ 2 (by norm_num),
      co_of_mul p _ _ 2 (by norm_num), y2, yy2]; ring

private lemma two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

private lemma ψ_τ (hp2 : p ≠ 2) (n : ℕ) (x : S p) (hx : co p 0 x ≠ 0) :
    ψ p (τ p n x) = (n : ZMod p) ^ 2 * ψ p x := by
  obtain ⟨t0, t1, t2⟩ := co_τ p hp2 n x
  have h2 := two_ne_zero' p hp2
  simp only [ψ, t0, t1, t2]
  field_simp
  ring

private lemma cyclotomic_zmod_eq (hp : p.Prime) : cyclotomic p (ZMod p) = (X - 1) ^ (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have := cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) (n := 1) (p := p) hp.not_dvd_one
  rwa [one_mul, cyclotomic_one] at this

private lemma aeval_one_add_eps_cyclotomic (hp5 : 5 ≤ p) :
    aeval (1 + eps p) (cyclotomic p ℤ) = 0 := by
  rw [← aeval_map_algebraMap (ZMod p), map_cyclotomic, cyclotomic_zmod_eq p hp.out]
  simp only [map_pow, map_sub, aeval_X, map_one, add_sub_cancel_left]
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 3 + k := ⟨p - 4, by omega⟩
  rw [hk, pow_add, eps_pow_three, zero_mul]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

omit [IsCyclotomicExtension {p} ℚ K] in
private lemma minpoly_toInteger : minpoly ℤ hζ.toInteger = cyclotomic p ℤ := by
  rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) hζ.toInteger,
    cyclotomic_eq_minpoly hζ hp.out.pos]
  rfl

private noncomputable def ev (hp5 : 5 ≤ p) : 𝓞 K →ₐ[ℤ] S p :=
  hζ.integralPowerBasis.lift (1 + eps p) (by
    rw [IsPrimitiveRoot.integralPowerBasis_gen, minpoly_toInteger p hζ]
    exact aeval_one_add_eps_cyclotomic p hp5)

private lemma ev_zeta (hp5 : 5 ≤ p) : ev p hζ hp5 hζ.toInteger = 1 + eps p := by
  rw [ev, ← IsPrimitiveRoot.integralPowerBasis_gen, PowerBasis.lift_gen]

private lemma ev_σ (hp5 : 5 ≤ p) (σ : 𝓞 K →+* 𝓞 K) (n : ℕ)
    (hσ : σ hζ.toInteger = hζ.toInteger ^ n) (x : 𝓞 K) :
    ev p hζ hp5 (σ x) = τ p n (ev p hζ hp5 x) := by
  have key : (ev p hζ hp5).comp σ.toIntAlgHom =
      ((τ p n).comp (ev p hζ hp5).toRingHom).toIntAlgHom := by
    refine hζ.integralPowerBasis.algHom_ext ?_
    rw [IsPrimitiveRoot.integralPowerBasis_gen]
    change ev p hζ hp5 (σ hζ.toInteger) = τ p n (ev p hζ hp5 hζ.toInteger)
    rw [hσ, map_pow, ev_zeta, map_add, map_one, τ_eps]
    ring
  exact DFunLike.congr_fun key x

private lemma co0_ev_unit_ne_zero (hp5 : 5 ≤ p) (u : (𝓞 K)ˣ) : co p 0 (ev p hζ hp5 u) ≠ 0 := by
  intro h
  have h1 := (co_mul p (ev p hζ hp5 u) (ev p hζ hp5 ↑u⁻¹)).1
  rw [← map_mul, Units.mul_inv, map_one, (co_one p).1, h, zero_mul] at h1
  exact one_ne_zero h1

private noncomputable def Ψ (hp5 : 5 ≤ p) (u : (𝓞 K)ˣ) : ZMod p := ψ p (ev p hζ hp5 u)

private lemma Ψ_mul (hp5 : 5 ≤ p) (u v : (𝓞 K)ˣ) :
    Ψ p hζ hp5 (u * v) = Ψ p hζ hp5 u + Ψ p hζ hp5 v := by
  simp only [Ψ, Units.val_mul, map_mul]
  exact ψ_mul p _ _ (co0_ev_unit_ne_zero p hζ hp5 u) (co0_ev_unit_ne_zero p hζ hp5 v)

private lemma Ψ_pow (hp5 : 5 ≤ p) (u : (𝓞 K)ˣ) (n : ℕ) :
    Ψ p hζ hp5 (u ^ n) = n * Ψ p hζ hp5 u := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, Ψ, Units.val_one, map_one, ψ]
    rw [(co_one p).1, (co_one p).2.1, (co_one p).2.2]; ring
  | succ n ih => rw [pow_succ, Ψ_mul, ih]; push_cast; ring

private lemma Ψ_pow_p (hp5 : 5 ≤ p) (u : (𝓞 K)ˣ) : Ψ p hζ hp5 (u ^ p) = 0 := by
  rw [Ψ_pow, ZMod.natCast_self, zero_mul]

private lemma Ψ_σ (hp5 : 5 ≤ p) (σ : 𝓞 K ≃+* 𝓞 K) (n : ℕ)
    (hσ : σ hζ.toInteger = hζ.toInteger ^ n) (u : (𝓞 K)ˣ) :
    Ψ p hζ hp5 (Units.mapEquiv σ.toMulEquiv u) = (n : ZMod p) ^ 2 * Ψ p hζ hp5 u := by
  have hp2 : p ≠ 2 := by omega
  change ψ p (ev p hζ hp5 (σ.toRingHom (u : 𝓞 K))) = _
  rw [ev_σ p hζ hp5 σ.toRingHom n hσ, ψ_τ p hp2 n _ (co0_ev_unit_ne_zero p hζ hp5 u)]
  rfl

private lemma ψ_two_add_eps (hp2 : p ≠ 2) : ψ p (AdjoinRoot.of _ 2 + eps p) = 4⁻¹ := by
  have h2 := two_ne_zero' p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨o0, o1, o2⟩ := co_of p (2 : ZMod p)
  obtain ⟨e0, e1, e2⟩ := co_eps p
  simp only [ψ, map_add, o0, o1, o2, e0, e1, e2, add_zero, zero_add, zero_div, mul_zero]
  field_simp
  ring

private lemma Ψ_one_add_zeta (hp5 : 5 ≤ p) (c : (𝓞 K)ˣ) (hc : (c : 𝓞 K) = 1 + hζ.toInteger) :
    Ψ p hζ hp5 c = 4⁻¹ := by
  have hev : ev p hζ hp5 c = AdjoinRoot.of _ 2 + eps p := by
    rw [hc, map_add, map_one, ev_zeta, map_ofNat]; ring
  unfold Ψ
  rw [hev]
  exact ψ_two_add_eps p (by omega)

private lemma four_inv_ne_zero (hp5 : 5 ≤ p) : (4 : ZMod p)⁻¹ ≠ 0 := by
  have h2 := two_ne_zero' p (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact inv_ne_zero h4

end Aux1B2

namespace Aux2Glue

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
variable (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M)

private lemma isUnit_natCast_card_units_zmod :
    IsUnit ((Nat.card (ZMod p)ˣ : ℕ) : ZMod p) := by
  have hp := (Fact.out : p.Prime)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one, CharP.cast_eq_zero (ZMod p) p, zero_sub]
  exact (IsUnit.neg_iff 1).mpr isUnit_one

/-- A linear map that scales the action of `d` by `d ^ i` is unchanged by the projector
`Stickelberger.omegaIdempotent`. -/
private theorem comp_omegaIdempotent_of_equivariant {i : ℕ} {N : Type*} [AddCommGroup N]
    [Module (ZMod p) N] (f : M →ₗ[ZMod p] N)
    (hf : ∀ d : (ZMod p)ˣ, ∀ x, f (ρ d x) = ((d : ZMod p) ^ i) • f x)
    (a : M) : f (Stickelberger.omegaIdempotent p ρ i a) = f a := by
  rw [Stickelberger.omegaIdempotent_apply, map_smul, map_sum]
  have : ∀ d : (ZMod p)ˣ, f ((((d : ZMod p) ^ i)⁻¹) • ρ d a) = f a := by
    intro d
    rw [map_smul, hf d a, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero i (Units.ne_zero d)), one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul]
  rw [isUnit_natCast_card_units_zmod.inv_mul_cancel, one_smul]

private theorem omegaIdempotent_ne_zero_of_equivariant {i : ℕ} {N : Type*} [AddCommGroup N]
    [Module (ZMod p) N] (f : M →ₗ[ZMod p] N)
    (hf : ∀ d : (ZMod p)ˣ, ∀ x, f (ρ d x) = ((d : ZMod p) ^ i) • f x)
    {a : M} (hfa : f a ≠ 0) : Stickelberger.omegaIdempotent p ρ i a ≠ 0 :=
  fun h0 => hfa (by rw [← comp_omegaIdempotent_of_equivariant ρ f hf a, h0, map_zero])

end Aux2Glue

open NumberField IsCyclotomicExtension Stickelberger

open NumberField Stickelberger

attribute [local instance] Stickelberger.instIsCycExt

namespace Aux2Glue

variable (p : ℕ) [Fact p.Prime]

section Functional

variable (hp5 : 5 ≤ p) {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)

private noncomputable def φAdd : Additive (𝓞 (CyclotomicField p ℚ))ˣ →+ ZMod p where
  toFun a := Aux1B2.Ψ p hζ hp5 a.toMul
  map_zero' := by
    have := Aux1B2.Ψ_pow p hζ hp5 (1 : (𝓞 (CyclotomicField p ℚ))ˣ) 0
    simpa using this
  map_add' a b := by
    change Aux1B2.Ψ p hζ hp5 (a.toMul * b.toMul) = _ + _
    exact Aux1B2.Ψ_mul p hζ hp5 a.toMul b.toMul

private lemma φAdd_ofMul (u : (𝓞 (CyclotomicField p ℚ))ˣ) :
    φAdd p hp5 hζ (Additive.ofMul u) = Aux1B2.Ψ p hζ hp5 u := rfl

private noncomputable def funcF :
    ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p →ₗ[ZMod p] ZMod p :=
  ((LinearMap.range (LinearMap.lsmul ℤ (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p)).liftQ
    (φAdd p hp5 hζ).toIntLinearMap (by
      intro x hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      rw [LinearMap.mem_ker]
      simp)).toAddMonoidHom.toZModLinearMap p

private lemma funcF_proj (u : (𝓞 (CyclotomicField p ℚ))ˣ) :
    funcF p hp5 hζ (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul u)) =
      Aux1B2.Ψ p hζ hp5 u := rfl

include hζ in
private lemma hζ_toInteger_pow_p : hζ.toInteger ^ p = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact hζ.toInteger_isPrimitiveRoot.pow_eq_one

private theorem funcF_equivariant (d : (ZMod p)ˣ)
    (a : ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p) :
    funcF p hp5 hζ (unitsGalAction p d a) = ((d : ZMod p) ^ 2) • funcF p hp5 hζ a := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨a, rfl⟩ := ModN.mkQ_surjective (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p a
  rw [show a = Additive.ofMul a.toMul from rfl]
  rw [show unitsGalAction p d =
        unitsEnd p (𝓞 (CyclotomicField p ℚ)) (clRingAction p (CyclotomicField p ℚ) d) from rfl,
    unitsEnd_proj, funcF_proj, funcF_proj]
  rw [Aux1B2.Ψ_σ p hζ hp5 (clRingAction p (CyclotomicField p ℚ) d) (d : ZMod p).val
    (clRingAction_apply_of_pow_eq p (CyclotomicField p ℚ) d (hζ_toInteger_pow_p p hζ))]
  rw [smul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

end Functional

end Aux2Glue

namespace Stickelberger

variable (p : ℕ) [Fact p.Prime]

open Aux2Glue in
/-- For a prime `p ≥ 5` and a primitive `p`-th root of unity `ζ` in `𝓞 (ℚ(ζ_p))`, the
`ω²`-component of the class of the cyclotomic unit `c₂` represented by `1 + ζ` in the units of
`𝓞 (ℚ(ζ_p))` modulo `p`-th powers is nonzero. -/
public theorem omegaIdempotent_two_cycloUnitTwo_ne_zero (hp5 : 5 ≤ p)
    (ζ : 𝓞 (CyclotomicField p ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (c₂ : (𝓞 (CyclotomicField p ℚ))ˣ) (hc : (c₂ : 𝓞 (CyclotomicField p ℚ)) = 1 + ζ) :
    omegaIdempotent p (unitsGalAction p) 2
        (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p
          (Additive.ofMul c₂)) ≠ 0 := by
  refine Aux2Glue.omegaIdempotent_ne_zero_of_equivariant (unitsGalAction p)
    (funcF p hp5 hζ) (funcF_equivariant p hp5 hζ) ?_
  rw [funcF_proj p hp5 hζ c₂,
    Aux1B2.Ψ_one_add_zeta p hζ hp5 c₂ (by rw [hc]; congr 1)]
  exact Aux1B2.four_inv_ne_zero p hp5

end Stickelberger
