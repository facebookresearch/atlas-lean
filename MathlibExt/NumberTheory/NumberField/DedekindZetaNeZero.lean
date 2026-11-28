/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re.lean`
and
`P2M/Sol/S_NumberField_dedekindZeta_ne_zero_of_one_lt_re.lean`
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

public import Mathlib.NumberTheory.NumberField.DedekindZeta

import Mathlib.NumberTheory.EulerProduct.ExpLog

@[expose] public section

open NumberField Filter Complex
open scoped Topology Classical

namespace NumberField

namespace DedekindZetaNeZero


universe u

variable (K : Type u) [Field K] [NumberField K]

private noncomputable def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

private theorem dedekindZeta_eq_LSeries (z : ℂ) :
    dedekindZeta K z = LSeries (fun n => (idealCount K n : ℂ)) z := rfl

private scoped instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

private theorem idealCount_zero : idealCount K 0 = 1 := by
  rw [idealCount]
  have : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_eq_zero_iff.mpr rfl⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp I.2) }
  exact Nat.card_unique

private theorem tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue]
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = idealCount K 0 from (idealCount_zero K).symm,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le)]
  simp only [idealCount]
  have e : {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} ≃
      Σ x : {x : ℕ // x ∈ Finset.Icc 0 n}, {I : Ideal (𝓞 K) // Ideal.absNorm I = x.1} :=
    { toFun := fun I => ⟨⟨Ideal.absNorm I.1, Finset.mem_Icc.mpr ⟨Nat.zero_le _, I.2⟩⟩,
        ⟨I.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, by
        have hx := Finset.mem_Icc.mp x.1.2
        have h2 : Ideal.absNorm x.2.1 = x.1 := x.2.2
        rw [h2]; exact hx.2⟩
      left_inv := fun I => Subtype.ext rfl
      right_inv := fun x => by
        obtain ⟨⟨x, hx⟩, ⟨I, hI⟩⟩ := x
        obtain rfl : x = Ideal.absNorm I := hI.symm
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma, Finset.univ_eq_attach]
  exact Finset.sum_attach (Finset.Icc 0 n)
    (fun x => Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = x})

private theorem isBigO_sum_idealCount :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
  have h1 : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ (tendsto_sum_idealCount_div K)
    filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (Nat.cast_ne_zero.mpr hn)
  exact h1.congr_right fun n => (Real.rpow_one _).symm

private theorem LSeriesSummable_idealCount {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) z := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    (isBigO_sum_idealCount K) (fun n => Nat.cast_nonneg _) zero_le_one hz
  simpa only [Complex.ofReal_natCast] using h

private theorem tsum_fiber_const {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] (n : ℕ) (c : M) :
    ∑' _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, c = idealCount K n • c := by
  haveI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, idealCount, Nat.card_eq_fintype_card]

private theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  rw [← e.summable_iff]
  have hnn : ∀ p, 0 ≤ ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) p := fun p =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) ⟨n, c⟩ =
        (n : ℝ) ^ (-σ) := fun n c => by
    simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun n => ?_, ?_⟩
  · exact Summable.of_finite
  · simp_rw [hfib, tsum_fiber_const, nsmul_eq_mul]
    have hL : Summable fun n => ‖LSeries.term (fun n => (idealCount K n : ℂ)) σ n‖ :=
      summable_norm_iff.mpr (LSeriesSummable_idealCount K (z := σ) (by simpa using hσ))
    refine hL.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (by linarith : σ ≠ 0)), mul_zero]
    · rw [Complex.norm_natCast, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n),
        div_eq_mul_inv]

private theorem summable_norm_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)‖ := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  refine (summable_absNorm_rpow K hz).congr fun I => ?_
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow hz0, norm_zero,
      Real.zero_rpow (neg_ne_zero.mpr (by linarith : z.re ≠ 0))]
  · rw [Complex.norm_natCast_cpow_of_pos h, Complex.neg_re]

private theorem summable_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) :=
  (summable_norm_absNorm_cpow K hz).of_norm

private theorem tsum_absNorm_cpow_eq_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
    ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) = dedekindZeta K z := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  have hs : Summable ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) :=
    e.summable_iff.mpr (summable_absNorm_cpow K hz)
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) ⟨n, c⟩ = (n : ℂ) ^ (-z) :=
    fun n c => by simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  rw [← e.tsum_eq, show (fun c => (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) (e c))
      = (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e from rfl, hs.tsum_sigma,
    dedekindZeta_eq_LSeries, LSeries]
  refine tsum_congr fun n => ?_
  simp_rw [hfib]
  rw [tsum_fiber_const, nsmul_eq_mul, LSeries.term_def]
  split_ifs with h0
  · rw [h0, Nat.cast_zero, Complex.zero_cpow hz0, mul_zero]
  · rw [Complex.cpow_neg, div_eq_mul_inv]

private abbrev Primes : Type u := {Q : Ideal (𝓞 K) // Prime Q}

private def primeSet (T : Finset (Primes K)) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ 0 ∧ ∀ Q : Primes K, Q.1 ∣ I → Q ∈ T}

private theorem primeSet_empty : primeSet K ∅ = {⊤} := by
  ext I
  simp only [primeSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hI0, hprime⟩
    by_contra hne
    have hnu : ¬IsUnit I := fun h => hne (Ideal.isUnit_iff.mp h)
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_factors hI0 hnu
    exact absurd (hprime ⟨P, UniqueFactorizationMonoid.prime_of_factor P hP⟩
      (UniqueFactorizationMonoid.dvd_of_mem_factors hP)) (Finset.notMem_empty _)
  · rintro rfl
    refine ⟨?_, fun Q hdvd => ?_⟩
    · intro h
      rw [← Ideal.one_eq_top] at h
      exact one_ne_zero h
    · exact absurd (Ideal.isUnit_iff.mpr (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))) Q.2.not_unit

private theorem two_le_absNorm (Q : Primes K) : 2 ≤ Ideal.absNorm Q.1 := by
  have h0 : Ideal.absNorm Q.1 ≠ 0 := fun h =>
    Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm Q.1 ≠ 1 := fun h =>
    Q.2.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

private theorem norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    ‖((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have h2 := two_le_absNorm K Q
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h1 : (1 : ℝ) < (Ideal.absNorm Q.1 : ℕ) := by exact_mod_cast h2
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

private theorem one_sub_absNorm_cpow_ne_zero {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    (1 : ℂ) - ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hlt := norm_absNorm_cpow_neg_lt_one K hs Q
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

private theorem cpow_pow_natCast (m k : ℕ) (v : ℂ) :
    ((m ^ k : ℕ) : ℂ) ^ v = (((m : ℕ) : ℂ) ^ v) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

private theorem tsum_primeSet_insert {s : ℂ} (hs : 1 < s.re) (P : Primes K)
    {T : Finset (Primes K)} (hPT : P ∉ T) :
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hP0 : P.1 ≠ 0 := P.2.ne_zero
  have hmemF : ∀ kc : ℕ × primeSet K T, P.1 ^ kc.1 * kc.2.1 ∈ primeSet K (insert P T) := by
    rintro ⟨k, ⟨c, hc0, hcmem⟩⟩
    refine ⟨mul_ne_zero (pow_ne_zero k hP0) hc0, fun Q hdvd => ?_⟩
    rcases (Prime.dvd_mul Q.2).mp hdvd with hQP | hQc
    · have : Q = P := Subtype.ext
        (associated_iff_eq.mp (Prime.associated_of_dvd Q.2 P.2 (Q.2.dvd_of_dvd_pow hQP)))
      rw [this]; exact Finset.mem_insert_self P T
    · exact Finset.mem_insert_of_mem (hcmem Q hQc)
  let F : ℕ × primeSet K T → primeSet K (insert P T) := fun kc => ⟨P.1 ^ kc.1 * kc.2.1, hmemF kc⟩
  have hkey : ∀ (k k' : ℕ) (c c' : Ideal (𝓞 K)), c ∈ primeSet K T → c' ∈ primeSet K T →
      k ≤ k' → P.1 ^ k * c = P.1 ^ k' * c' → k = k' ∧ c = c' := by
    intro k k' c c' hc hc' hkk h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
    rw [pow_add, mul_assoc] at h
    have hcc : c = P.1 ^ d * c' := mul_left_cancel₀ (pow_ne_zero k hP0) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [pow_zero, one_mul] at hcc; exact ⟨by simp, hcc⟩
    · exfalso; exact hPT (hc.2 P (hcc ▸ dvd_mul_of_dvd_left (dvd_pow_self P.1 hd.ne') c'))
  have hFbij : Function.Bijective F := by
    constructor
    · rintro ⟨k, c⟩ ⟨k', c'⟩ hab
      have hval : P.1 ^ k * c.1 = P.1 ^ k' * c'.1 := congrArg Subtype.val hab
      rcases le_total k k' with hkk | hkk
      · obtain ⟨h1, h2⟩ := hkey k k' c.1 c'.1 c.2 c'.2 hkk hval
        exact Prod.ext h1 (Subtype.ext h2)
      · obtain ⟨h1, h2⟩ := hkey k' k c'.1 c.1 c'.2 c.2 hkk hval.symm
        exact Prod.ext h1.symm (Subtype.ext h2.symm)
    · rintro ⟨J, hJ0, hJmem⟩
      have hfin : FiniteMultiplicity P.1 J := FiniteMultiplicity.of_not_isUnit P.2.not_unit hJ0
      obtain ⟨c, hc, hPc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
      have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hJ0 hc
      have hcmem : c ∈ primeSet K T := by
        refine ⟨hc0, fun Q hQc => ?_⟩
        have hQJ : Q.1 ∣ J := hc ▸ dvd_mul_of_dvd_right hQc _
        rcases Finset.mem_insert.mp (hJmem Q hQJ) with rfl | hQT
        · exact absurd hQc hPc
        · exact hQT
      exact ⟨⟨multiplicity P.1 J, ⟨c, hcmem⟩⟩, Subtype.ext hc.symm⟩
  have hgeo : Summable (fun k : ℕ => ‖(((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k‖) :=
    (summable_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)).norm
  have hsub : Summable (fun J : primeSet K T => ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖) :=
    (summable_norm_absNorm_cpow K hs).subtype _
  calc
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
        = ∑' kc : ℕ × primeSet K T,
            ((Ideal.absNorm ((Equiv.ofBijective F hFbij) kc).1 : ℕ) : ℂ) ^ (-s) :=
      ((Equiv.ofBijective F hFbij).tsum_eq
        (fun I : primeSet K (insert P T) => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))).symm
    _ = ∑' kc : ℕ × primeSet K T,
          ((((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ kc.1
            * ((Ideal.absNorm kc.2.1 : ℕ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun kc => ?_
      have hval : ((Equiv.ofBijective F hFbij) kc).1 = P.1 ^ kc.1 * kc.2.1 := rfl
      rw [hval, map_mul, map_pow, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, cpow_pow_natCast]
    _ = (∑' k : ℕ, (((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k)
          * ∑' J : primeSet K T, ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) :=
      (tsum_mul_tsum_of_summable_norm hgeo hsub).symm
    _ = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
      rw [tsum_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)]

private theorem tsum_primeSet_eq_prod {s : ℂ} (hs : 1 < s.re) (T : Finset (Primes K)) :
    ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
    rw [primeSet_empty,
      tsum_singleton ⊤ (fun J : Ideal (𝓞 K) => ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)),
      Finset.prod_empty, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow]
  | insert P T hPT ih =>
    rw [tsum_primeSet_insert K hs P hPT, Finset.prod_insert hPT, ih]

private theorem mem_primeSet_of_factors {I : Ideal (𝓞 K)} (hI : I ≠ 0) {T : Finset (Primes K)}
    (hT : ∀ Q : Primes K, Q.1 ∈ UniqueFactorizationMonoid.factors I → Q ∈ T) :
    I ∈ primeSet K T := by
  refine ⟨hI, fun Q hdvd => ?_⟩
  obtain ⟨R, hR, hQR⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI Q.2.irreducible hdvd
  have hQ : Q.1 = R := associated_iff_eq.mp hQR
  exact hT Q (hQ ▸ hR)

private theorem tendsto_tsum_primeSet_of_summable {f : Ideal (𝓞 K) → ℂ}
    (hf : Summable fun I => ‖f I‖) (hf0 : f 0 = 0) :
    Tendsto (fun T : Finset (Primes K) => ∑' I : primeSet K T, f I) atTop (𝓝 (∑' I, f I)) := by
  have hfs : Summable f := hf.of_norm
  have htail : Tendsto (fun F : Finset (Ideal (𝓞 K)) =>
      ∑' I, ((↑F : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I) atTop (𝓝 0) := by
    refine (tendsto_tsum_compl_atTop_zero (fun I => ‖f I‖)).congr fun F => ?_
    exact tsum_subtype ((↑F : Set (Ideal (𝓞 K)))ᶜ) (fun I => ‖f I‖)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F₀, hF₀⟩ := Metric.tendsto_atTop.mp htail ε hε
  refine ⟨F₀.biUnion (fun I =>
      ((UniqueFactorizationMonoid.factors I).toFinset).subtype (fun Q => Prime Q)), fun T hT => ?_⟩
  have hin : ∀ I ∈ F₀, I ≠ 0 → I ∈ primeSet K T := by
    intro I hI hI0
    refine mem_primeSet_of_factors K hI0 fun Q hQ => hT ?_
    exact Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_subtype.mpr (Multiset.mem_toFinset.mpr hQ)⟩
  have hdom : ∀ I : Ideal (𝓞 K), ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I
      ≤ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I := by
    intro I
    by_cases hI0 : I = 0
    · have hfI : ‖f I‖ = 0 := by rw [hI0, hf0, norm_zero]
      calc ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I
          ≤ ‖f I‖ := Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => norm_nonneg _)
        _ = 0 := hfI
        _ ≤ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
          Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    · by_cases hmem : I ∈ primeSet K T
      · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
        exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
      · have hIF : I ∈ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ) :=
          Set.mem_compl fun h => hmem (hin I (Finset.mem_coe.mp h) hI0)
        rw [Set.indicator_of_mem (Set.mem_compl hmem), Set.indicator_of_mem hIF]
  have hbound := hF₀ F₀ le_rfl
  rw [Real.dist_0_eq_abs, abs_of_nonneg (tsum_nonneg fun I =>
    Set.indicator_nonneg (fun _ _ => norm_nonneg _) I)] at hbound
  have hsplit := hfs.tsum_subtype_add_tsum_subtype_compl (primeSet K T)
  rw [dist_eq_norm, show (∑' I : primeSet K T, f I) - ∑' I, f I = -∑' I : ↥(primeSet K T)ᶜ, f I by
    rw [← hsplit]; ring, norm_neg]
  calc ‖∑' I : ↥(primeSet K T)ᶜ, f I‖
      ≤ ∑' I : ↥(primeSet K T)ᶜ, ‖f I‖ := norm_tsum_le_tsum_norm (hf.subtype _)
    _ = ∑' I, ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I :=
      tsum_subtype ((primeSet K T)ᶜ) (fun I => ‖f I‖)
    _ ≤ ∑' I, ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
      Summable.tsum_le_tsum hdom (hf.indicator _) (hf.indicator _)
    _ < ε := hbound

private theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hsz : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hsum : Summable (fun P : Primes K => ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) :=
    (summable_absNorm_cpow K hs).comp_injective Subtype.val_injective
  have hne : ∀ P : Primes K, (1 : ℂ) - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P => one_sub_absNorm_cpow_ne_zero K hs0 P
  have hg : Summable (fun P : Primes K => -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))) :=
    hsum.clog_one_sub.neg

  have hlim1 : Tendsto (fun T : Finset (Primes K) =>
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (cexp (∑' P : Primes K, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))))) := by
    have h1 : Tendsto (fun T : Finset (Primes K) =>
        ∑ P ∈ T, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))) atTop
        (𝓝 (∑' P : Primes K, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)))) := hg.hasSum
    refine ((Complex.continuous_exp.tendsto _).comp h1).congr fun T => ?_
    show cexp (∑ P ∈ T, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)))
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun P _ => by rw [exp_neg, exp_log (hne P)]

  have hlim2 : Tendsto (fun T : Finset (Primes K) =>
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) atTop (𝓝 (dedekindZeta K s)) := by
    have h := tendsto_tsum_primeSet_of_summable K
      (f := fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s))
      (summable_norm_absNorm_cpow K hs)
      (by show ((Ideal.absNorm (0 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0
          rw [map_zero, Nat.cast_zero, Complex.zero_cpow hsz])
    rw [tsum_absNorm_cpow_eq_dedekindZeta K hs] at h
    exact h.congr fun T => tsum_primeSet_eq_prod K hs T

  rw [tendsto_nhds_unique hlim2 hlim1]
  exact Complex.exp_ne_zero _
end DedekindZetaNeZero

/-- The Dedekind zeta function of a number field does not vanish at any
point `s` with `1 < s.re`: for `Re s > 1` it is given by its Euler product
over the prime ideals, and no Euler factor vanishes there. -/
public theorem dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s ≠ 0 :=
  DedekindZetaNeZero.dedekindZeta_ne_zero K hs

end NumberField
