/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClass
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

private noncomputable def brunTitchmarshInvNat : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, mul_inv]

private noncomputable def brunTitchmarshNu : ArithmeticFunction ℝ :=
  ⟨brunTitchmarshInvNat, by simp [brunTitchmarshInvNat]⟩

@[simp] private theorem brunTitchmarshNu_apply (n : ℕ) :
    brunTitchmarshNu n = (n : ℝ)⁻¹ := rfl

private theorem brunTitchmarshNu_mult : brunTitchmarshNu.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [brunTitchmarshNu_apply, Nat.cast_mul, mul_inv]

private def brunTitchmarshPrimes (R k : ℕ) : Finset ℕ :=
  (Finset.range (R + 1)).filter fun p ↦ p.Prime ∧ ¬p ∣ k

private def brunTitchmarshPrimeProduct (R k : ℕ) : ℕ :=
  ∏ p ∈ brunTitchmarshPrimes R k, p

private theorem brunTitchmarshPrimeProduct_squarefree (R k : ℕ) :
    Squarefree (brunTitchmarshPrimeProduct R k) := by
  unfold brunTitchmarshPrimeProduct brunTitchmarshPrimes
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact (Nat.coprime_iff_isRelPrime.mp <| (Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.prime.squarefree

private theorem brunTitchmarshPrimeProduct_ne_zero (R k : ℕ) :
    brunTitchmarshPrimeProduct R k ≠ 0 := by
  unfold brunTitchmarshPrimeProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  simp only [brunTitchmarshPrimes, Finset.mem_filter, Finset.mem_range] at hp
  exact hp.2.1.ne_zero

private theorem brunTitchmarshPrime_dvd_product (R k p : ℕ) (hp : p.Prime) :
    p ∣ brunTitchmarshPrimeProduct R k ↔ p ≤ R ∧ ¬p ∣ k := by
  constructor
  · intro hdiv
    rw [brunTitchmarshPrimeProduct, Prime.dvd_finsetProd_iff hp.prime] at hdiv
    obtain ⟨q, hq, hpq⟩ := hdiv
    simp only [brunTitchmarshPrimes, Finset.mem_filter, Finset.mem_range] at hq
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.2.1).mp hpq
    subst q
    exact ⟨Nat.lt_succ_iff.mp hq.1, hq.2.2⟩
  · rintro ⟨hpR, hpk⟩
    unfold brunTitchmarshPrimeProduct
    apply Finset.dvd_prod_of_mem
    simp only [brunTitchmarshPrimes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr hpR, hp, hpk⟩

private noncomputable def brunTitchmarshSieve (X k ell R : ℕ) : BoundingSieve where
  support := (Finset.range (X + 1)).filter fun n ↦ n ≡ ell [MOD k]
  prodPrimes := brunTitchmarshPrimeProduct R k
  prodPrimes_squarefree := brunTitchmarshPrimeProduct_squarefree R k
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := (X + 1 : ℕ) / (k : ℝ)
  nu := brunTitchmarshNu
  nu_mult := brunTitchmarshNu_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [brunTitchmarshNu_apply, inv_pos]
    exact_mod_cast hp.pos
  nu_lt_one_of_prime := by
    intro p hp _
    rw [brunTitchmarshNu_apply]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

private theorem brunTitchmarshSieve_siftedSum (X k ell R : ℕ) :
    (brunTitchmarshSieve X k ell R).siftedSum =
      (((brunTitchmarshSieve X k ell R).support.filter fun n ↦
        Nat.Coprime (brunTitchmarshPrimeProduct R k) n).card : ℝ) := by
  unfold BoundingSieve.siftedSum
  change (∑ n ∈ (brunTitchmarshSieve X k ell R).support,
    if Nat.Coprime (brunTitchmarshPrimeProduct R k) n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]

private theorem brunTitchmarshSieve_multSum (X k ell R d : ℕ) :
    (brunTitchmarshSieve X k ell R).multSum d =
      (((brunTitchmarshSieve X k ell R).support.filter fun n ↦ d ∣ n).card : ℝ) := by
  unfold BoundingSieve.multSum
  change (∑ n ∈ (brunTitchmarshSieve X k ell R).support,
    if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]

private theorem brunTitchmarsh_card_mod_sub_div_abs_le (N d a : ℕ)
    (hd : 0 < d) (ha : a < d) :
    |(((Finset.range N).filter (fun n ↦ n % d = a)).card : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have hcount := Nat.count_modEq_card N hd a
  have hmod : a % d = a := Nat.mod_eq_of_lt ha
  have hcard : Nat.count (fun x ↦ x ≡ a [MOD d]) N =
      ((Finset.range N).filter (fun n ↦ n % d = a)).card := by
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hna⟩
      exact ⟨hn, by simpa only [Nat.ModEq, hmod] using hna⟩
    · rintro ⟨hn, hna⟩
      exact ⟨hn, by simpa only [Nat.ModEq, hmod] using hna⟩
  rw [hcard, hmod] at hcount
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdecomp : (N : ℝ) = d * (N / d : ℕ) + (N % d : ℕ) := by
    have h := Nat.div_add_mod N d
    exact_mod_cast h.symm
  have hlt : ((N % d : ℕ) : ℝ) < d := by
    exact_mod_cast Nat.mod_lt N hd
  have hdiv : (N : ℝ) / d = (N / d : ℕ) + (N % d : ℕ) / (d : ℝ) := by
    field_simp
    linarith
  have hfrac_nonneg : (0 : ℝ) ≤ (N % d : ℕ) / (d : ℝ) := by positivity
  have hfrac_le_one : ((N % d : ℕ) : ℝ) / d ≤ 1 := by
    rw [div_le_one hdR]
    exact hlt.le
  by_cases hif : a < N % d
  · simp only [hif, ite_true] at hcount
    have hcast : ((((Finset.range N).filter (fun n ↦ n % d = a)).card : ℕ) : ℝ) =
        (N / d : ℕ) + 1 := by exact_mod_cast hcount
    rw [hcast, hdiv]
    rw [show ((N / d : ℕ) : ℝ) + 1 -
      ((N / d : ℕ) + (N % d : ℕ) / (d : ℝ)) =
        1 - (N % d : ℕ) / (d : ℝ) by ring]
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · simp only [hif, ite_false] at hcount
    have hcast : ((((Finset.range N).filter (fun n ↦ n % d = a)).card : ℕ) : ℝ) =
        (N / d : ℕ) := by exact_mod_cast hcount
    rw [hcast, hdiv]
    rw [show ((N / d : ℕ) : ℝ) -
      ((N / d : ℕ) + (N % d : ℕ) / (d : ℝ)) =
        -((N % d : ℕ) / (d : ℝ)) by ring, abs_neg,
      abs_of_nonneg hfrac_nonneg]
    exact hfrac_le_one

private theorem brunTitchmarsh_coprime_of_dvd_primeProduct {R k d : ℕ}
    (hd : d ∣ brunTitchmarshPrimeProduct R k) : d.Coprime k := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpk
  have hpP : p ∣ brunTitchmarshPrimeProduct R k := hpd.trans hd
  exact (brunTitchmarshPrime_dvd_product R k p hp).mp hpP |>.2 hpk

private theorem brunTitchmarshSieve_abs_rem_le (X k ell R d : ℕ)
    (hk : 0 < k) (hdP : d ∣ brunTitchmarshPrimeProduct R k) :
    |(brunTitchmarshSieve X k ell R).rem d| ≤ 1 := by
  have hP0 := brunTitchmarshPrimeProduct_ne_zero R k
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hdP
  have hcop : d.Coprime k := brunTitchmarsh_coprime_of_dvd_primeProduct hdP
  let c := Nat.chineseRemainder hcop 0 ell
  let a : ℕ := c
  have ha : a < d * k := Nat.chineseRemainder_lt_mul hcop 0 ell hd0 hk.ne'
  have had : a ≡ 0 [MOD d] := c.prop.1
  have hak : a ≡ ell [MOD k] := c.prop.2
  have hfilter :
      (brunTitchmarshSieve X k ell R).support.filter (fun n ↦ d ∣ n) =
        (Finset.range (X + 1)).filter (fun n ↦ n % (d * k) = a) := by
    ext n
    simp only [brunTitchmarshSieve, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hnX, hnk⟩, hdn⟩
      refine ⟨hnX, ?_⟩
      have hnd : n ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdn
      have hnprod : n ≡ a [MOD d * k] := by
        change n ≡ c [MOD d * k]
        exact Nat.chineseRemainder_modEq_unique hcop hnd hnk
      change n % (d * k) = a
      have hnprod' : n % (d * k) = a % (d * k) := hnprod
      rwa [Nat.mod_eq_of_lt ha] at hnprod'
    · rintro ⟨hnX, hnprod⟩
      refine ⟨⟨hnX, ?_⟩, ?_⟩
      · have hna : n ≡ a [MOD d * k] := by
          change n % (d * k) = a % (d * k)
          rwa [Nat.mod_eq_of_lt ha]
        have hnak : n ≡ a [MOD k] := hna.of_dvd ⟨d, by simp [mul_comm]⟩
        exact hnak.trans hak
      · have hna : n ≡ a [MOD d * k] := by
          change n % (d * k) = a % (d * k)
          rwa [Nat.mod_eq_of_lt ha]
        have hnad : n ≡ a [MOD d] := hna.of_dvd ⟨k, rfl⟩
        exact Nat.modEq_zero_iff_dvd.mp (hnad.trans had)
  have hcard := brunTitchmarsh_card_mod_sub_div_abs_le
    (X + 1) (d * k) a (Nat.mul_pos hd0.bot_lt hk) ha
  unfold BoundingSieve.rem
  rw [brunTitchmarshSieve_multSum, hfilter]
  simp only [brunTitchmarshSieve, brunTitchmarshNu_apply]
  convert hcard using 1
  field_simp
  simp only [Nat.cast_mul]
  ring_nf

private def brunTitchmarshRadAway (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p ↦ ¬p ∣ k), p

private theorem brunTitchmarshInvNat_nonneg (n : ℕ) :
    0 ≤ brunTitchmarshInvNat n := by
  change 0 ≤ (n : ℝ)⁻¹
  positivity

private theorem brunTitchmarshInvNat_norm_prime {p : ℕ} (hp : p.Prime) :
    ‖brunTitchmarshInvNat p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr <| by exact_mod_cast hp.pos)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

private theorem brunTitchmarsh_prod_primeFactors_inv_one_sub (k : ℕ) (hk : 0 < k) :
    (∏ p ∈ k.primeFactors, (1 - brunTitchmarshInvNat p)⁻¹) =
      (k : ℝ) / Nat.totient k := by
  have htotQ := Nat.totient_eq_mul_prod_factors k
  have htot : (Nat.totient k : ℝ) =
      (k : ℝ) * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have htotR := congrArg (fun q : ℚ ↦ (q : ℝ)) htotQ
    simpa using htotR
  have hfactor : ∀ p ∈ k.primeFactors, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp'.one_lt)
    linarith
  have hprod : (0 : ℝ) < ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos hfactor
  change (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) = _
  rw [Finset.prod_inv_distrib, htot]
  field_simp

private theorem brunTitchmarsh_fiber_le (X k ell R l : ℕ) (hk : 0 < k)
    (hl : l ∣ brunTitchmarshPrimeProduct R k) (T : Finset ℕ)
    (hT : ∀ m ∈ T, m ∈ Nat.factoredNumbers (l.primeFactors ∪ k.primeFactors)) :
    ∑ m ∈ T, brunTitchmarshInvNat (l * m) ≤
      (k : ℝ) / Nat.totient k *
        (brunTitchmarshSieve X k ell R).selbergTerms l := by
  let S := l.primeFactors ∪ k.primeFactors
  have hsel : (brunTitchmarshSieve X k ell R).selbergTerms l =
      brunTitchmarshInvNat l *
        ∏ p ∈ l.primeFactors, (1 - brunTitchmarshInvNat p)⁻¹ := by
    rw [BoundingSieve.selbergTerms_apply]
    simp only [brunTitchmarshSieve, brunTitchmarshNu_apply]
    rfl
  have heuler :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := brunTitchmarshInvNat) (fun {_p} hp ↦ brunTitchmarshInvNat_norm_prime hp) S
  obtain ⟨-, hhas⟩ := heuler
  have hfilter : S.filter (fun p ↦ p.Prime) = S := by
    apply Finset.filter_true_of_mem
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  rw [hfilter] at hhas
  have hsub : ∑ m ∈ Finset.subtype (fun m ↦ m ∈ Nat.factoredNumbers S) T,
      brunTitchmarshInvNat (m : ℕ) ≤
      ∏ p ∈ S, (1 - brunTitchmarshInvNat p)⁻¹ := by
    exact sum_le_hasSum _ (fun i _ ↦ brunTitchmarshInvNat_nonneg i) hhas
  have hsubEq : ∑ m ∈ Finset.subtype (fun m ↦ m ∈ Nat.factoredNumbers S) T,
      brunTitchmarshInvNat (m : ℕ) = ∑ m ∈ T, brunTitchmarshInvNat m :=
    Finset.sum_subtype_of_mem brunTitchmarshInvNat hT
  have hcop := brunTitchmarsh_coprime_of_dvd_primeProduct hl
  have hdis : Disjoint l.primeFactors k.primeFactors := hcop.disjoint_primeFactors
  have hkprod := brunTitchmarsh_prod_primeFactors_inv_one_sub k hk
  calc
    ∑ m ∈ T, brunTitchmarshInvNat (l * m) =
        ∑ m ∈ T, brunTitchmarshInvNat l * brunTitchmarshInvNat m := by
      apply Finset.sum_congr rfl
      intro m _
      exact map_mul brunTitchmarshInvNat l m
    _ = brunTitchmarshInvNat l * ∑ m ∈ T, brunTitchmarshInvNat m := by
      rw [Finset.mul_sum]
    _ ≤ brunTitchmarshInvNat l *
        ∏ p ∈ S, (1 - brunTitchmarshInvNat p)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (brunTitchmarshInvNat_nonneg l)
      rw [← hsubEq]
      exact hsub
    _ = brunTitchmarshInvNat l *
        ((∏ p ∈ l.primeFactors, (1 - brunTitchmarshInvNat p)⁻¹) *
          ∏ p ∈ k.primeFactors, (1 - brunTitchmarshInvNat p)⁻¹) := by
      rw [Finset.prod_union hdis]
    _ = (k : ℝ) / Nat.totient k *
        (brunTitchmarshSieve X k ell R).selbergTerms l := by
      rw [hsel, hkprod]
      ring

private theorem brunTitchmarsh_harmonic_le_mul_levelSum
    (X k ell R : ℕ) (hk : 0 < k) :
    (harmonic R : ℝ) ≤ (k : ℝ) / Nat.totient k *
      levelSum (brunTitchmarshSieve X k ell R) R := by
  let B := Finset.Icc 1 R
  let s := brunTitchmarshSieve X k ell R
  let L := levelSet s R
  have hP0 := brunTitchmarshPrimeProduct_ne_zero R k
  have hmaps : ∀ n ∈ B, brunTitchmarshRadAway k n ∈ L := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn'.1
    have hfilter : n.primeFactors.filter (fun p ↦ ¬p ∣ k) ⊆ n.primeFactors :=
      Finset.filter_subset _ _
    have hradDvd : brunTitchmarshRadAway k n ∣ n := by
      apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hfilter)
      exact Nat.prod_primeFactors_dvd n
    have hradLe : brunTitchmarshRadAway k n ≤ R :=
      (Nat.le_of_dvd hnpos hradDvd).trans hn'.2
    have hsub : n.primeFactors.filter (fun p ↦ ¬p ∣ k) ⊆
        brunTitchmarshPrimes R k := by
      intro p hp
      rw [Finset.mem_filter] at hp
      simp only [brunTitchmarshPrimes, Finset.mem_filter, Finset.mem_range]
      have hpdvd := Nat.dvd_of_mem_primeFactors hp.1
      have hpR := (Nat.le_of_dvd hnpos hpdvd).trans hn'.2
      exact ⟨Nat.lt_succ_iff.mpr hpR, Nat.prime_of_mem_primeFactors hp.1, hp.2⟩
    have hradP : brunTitchmarshRadAway k n ∣ brunTitchmarshPrimeProduct R k := by
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    simp only [L, levelSet, Finset.mem_filter, Nat.mem_divisors, s]
    exact ⟨⟨hradP, hP0⟩, hradLe⟩
  have hfiber : (∑ n ∈ B, brunTitchmarshInvNat n) =
      ∑ l ∈ L, ∑ n ∈ B.filter (fun n ↦ brunTitchmarshRadAway k n = l),
        brunTitchmarshInvNat n := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  have hsum : (∑ n ∈ B, brunTitchmarshInvNat n) ≤
      (k : ℝ) / Nat.totient k * ∑ l ∈ L, s.selbergTerms l := by
    rw [hfiber, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    simp only [L, levelSet, Finset.mem_filter, Nat.mem_divisors] at hl
    let F := B.filter (fun n ↦ brunTitchmarshRadAway k n = l)
    let T := F.image (fun n ↦ n / l)
    have hmemT : ∀ m ∈ T,
        m ∈ Nat.factoredNumbers (l.primeFactors ∪ k.primeFactors) := by
      intro m hm
      simp only [T, Finset.mem_image] at hm
      obtain ⟨n, hnF, rfl⟩ := hm
      simp only [F, Finset.mem_filter] at hnF
      have hnB := Finset.mem_Icc.mp hnF.1
      have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hnB.1).ne'
      have hln : l ∣ n := by
        rw [← hnF.2]
        unfold brunTitchmarshRadAway
        exact dvd_trans
          (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
          (Nat.prod_primeFactors_dvd n)
      have hpf : l.primeFactors =
          n.primeFactors.filter (fun p ↦ ¬p ∣ k) := by
        have hprod := Nat.primeFactors_prod
          (s := n.primeFactors.filter (fun p ↦ ¬p ∣ k)) fun p hp ↦
            Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        have hrad : (∏ p ∈ n.primeFactors.filter (fun p ↦ ¬p ∣ k), p) = l := by
          simpa only [brunTitchmarshRadAway] using hnF.2
        rw [hrad] at hprod
        exact hprod
      have hnSub : n.primeFactors ⊆ l.primeFactors ∪ k.primeFactors := by
        intro p hp
        by_cases hpk : p ∣ k
        · exact Finset.mem_union_right _
            ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors hpk hk.ne')
        · apply Finset.mem_union_left
          rw [hpf]
          exact Finset.mem_filter.mpr ⟨hp, hpk⟩
      have hnFact : n ∈ Nat.factoredNumbers (l.primeFactors ∪ k.primeFactors) :=
        Nat.mem_factoredNumbers_of_primeFactors_subset hn0 hnSub
      have hdiv : n / l ∣ n := by
        use l
        rw [mul_comm]
        exact (Nat.mul_div_cancel' hln).symm
      exact Nat.mem_factoredNumbers_of_dvd hnFact hdiv
    have hsumEq : (∑ n ∈ F, brunTitchmarshInvNat n) =
        ∑ m ∈ T, brunTitchmarshInvNat (l * m) := by
      have hinj : Set.InjOn (fun n ↦ n / l) (F : Set ℕ) := by
        intro n1 hn1 n2 hn2 heq
        simp only [F, Finset.mem_coe, Finset.mem_filter] at hn1 hn2
        have hln1 : l ∣ n1 := by
          rw [← hn1.2]
          unfold brunTitchmarshRadAway
          exact dvd_trans
            (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
            (Nat.prod_primeFactors_dvd n1)
        have hln2 : l ∣ n2 := by
          rw [← hn2.2]
          unfold brunTitchmarshRadAway
          exact dvd_trans
            (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
            (Nat.prod_primeFactors_dvd n2)
        change n1 / l = n2 / l at heq
        rw [← Nat.mul_div_cancel' hln1, ← Nat.mul_div_cancel' hln2]
        exact congrArg (fun q ↦ l * q) heq
      have himage := Finset.sum_image (s := F) (g := fun n ↦ n / l)
        (f := fun m ↦ brunTitchmarshInvNat (l * m)) hinj
      change (∑ n ∈ F, brunTitchmarshInvNat n) =
        ∑ m ∈ F.image (fun n ↦ n / l), brunTitchmarshInvNat (l * m)
      rw [himage]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [F, Finset.mem_filter] at hn
      have hln : l ∣ n := by
        rw [← hn.2]
        unfold brunTitchmarshRadAway
        exact dvd_trans
          (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
          (Nat.prod_primeFactors_dvd n)
      rw [Nat.mul_div_cancel' hln]
    rw [show B.filter (fun n ↦ brunTitchmarshRadAway k n = l) = F from rfl, hsumEq]
    exact brunTitchmarsh_fiber_le X k ell R l hk hl.1.1 T hmemT
  have hharm : (∑ n ∈ B, brunTitchmarshInvNat n) = (harmonic R : ℝ) := by
    change (∑ n ∈ Finset.Icc 1 R, (n : ℝ)⁻¹) = (harmonic R : ℝ)
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← hharm]
  simpa only [s, L, levelSum] using hsum

private theorem brunTitchmarshLevelSum_ge (X k ell R : ℕ) (hk : 0 < k) :
    (Nat.totient k : ℝ) / k * Real.log (R + 1) ≤
      levelSum (brunTitchmarshSieve X k ell R) R := by
  have hharm := brunTitchmarsh_harmonic_le_mul_levelSum X k ell R hk
  have hlog := log_add_one_le_harmonic R
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hphi : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.mpr hk
  calc
    (Nat.totient k : ℝ) / k * Real.log (R + 1) ≤
        (Nat.totient k : ℝ) / k * (harmonic R : ℝ) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hlog
    _ ≤ (Nat.totient k : ℝ) / k *
        ((k : ℝ) / Nat.totient k *
          levelSum (brunTitchmarshSieve X k ell R) R) := by
      gcongr
    _ = levelSum (brunTitchmarshSieve X k ell R) R := by
      field_simp

private theorem brunTitchmarsh_primeCount_le_siftedSum (X k ell R : ℕ) :
    (Nat.primeCountingMod X k ell : ℝ) ≤ (R + 1 : ℕ) +
      (brunTitchmarshSieve X k ell R).siftedSum := by
  let T := (Finset.range (X + 1)).filter fun p ↦ p.Prime ∧ p ≡ ell [MOD k]
  have hTcard : T.card = Nat.primeCountingMod X k ell := by
    simpa only [T] using (Nat.primeCountingMod_eq_card_filter_range X k ell).symm
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun p ↦ p ≤ R)
  have hsmall : ((T.filter fun p ↦ p ≤ R).card : ℝ) ≤ (R + 1 : ℕ) := by
    have hsub : T.filter (fun p ↦ p ≤ R) ⊆ Finset.range (R + 1) := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hp).2)
    calc
      ((T.filter fun p ↦ p ≤ R).card : ℝ) ≤
          ((Finset.range (R + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (R + 1 : ℕ) := by simp
  have hlargeSub : T.filter (fun p ↦ ¬p ≤ R) ⊆
      (brunTitchmarshSieve X k ell R).support.filter
        (fun n ↦ Nat.Coprime (brunTitchmarshPrimeProduct R k) n) := by
    intro p hp
    simp only [T, Finset.mem_filter, Finset.mem_range, brunTitchmarshSieve] at hp ⊢
    refine ⟨⟨hp.1.1, hp.1.2.2⟩, ?_⟩
    apply Nat.coprime_of_dvd
    intro q hq hqP hqp
    have hqR := (brunTitchmarshPrime_dvd_product R k q hq).mp hqP |>.1
    have hqpEq := (Nat.prime_dvd_prime_iff_eq hq hp.1.2.1).mp hqp
    omega
  have hlarge : ((T.filter fun p ↦ ¬p ≤ R).card : ℝ) ≤
      (brunTitchmarshSieve X k ell R).siftedSum := by
    rw [brunTitchmarshSieve_siftedSum]
    exact_mod_cast Finset.card_le_card hlargeSub
  have hcast : ((T.filter (fun p ↦ p ≤ R)).card : ℝ) +
      ((T.filter fun p ↦ ¬p ≤ R).card : ℝ) = T.card := by
    exact_mod_cast hsplit
  rw [hTcard] at hcast
  linarith

private theorem brunTitchmarsh_primeCount_le (X k ell R : ℕ)
    (hk : 0 < k) (hR : 1 ≤ R) :
    (Nat.primeCountingMod X k ell : ℝ) ≤ (R + 1 : ℕ) +
      ((X + 1 : ℕ) : ℝ) / k *
        (1 / levelSum (brunTitchmarshSieve X k ell R) R) +
      (R : ℝ) ^ 12 := by
  let s := brunTitchmarshSieve X k ell R
  let w := levelWeights s R
  have hw1 : w 1 = 1 := levelWeights_one s R hR
  have hupper := BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hsieve := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (s := s) (BoundingSieve.lambdaSquared w) hupper
  have hmain := levelWeights_mainSum s R hR
  have hnu : ∀ d : ℕ, d ∣ s.prodPrimes → 1 ≤ (d : ℝ) * s.nu d := by
    intro d hd
    have hd0 := ne_zero_of_dvd_ne_zero (BoundingSieve.prodPrimes_ne_zero (s := s)) hd
    change 1 ≤ (d : ℝ) * (d : ℝ)⁻¹
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd0)]
  have hrem : ∀ d : ℕ, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ) := by
    intro d hd
    have hd0 := ne_zero_of_dvd_ne_zero (BoundingSieve.prodPrimes_ne_zero (s := s)) hd
    have h := brunTitchmarshSieve_abs_rem_le X k ell R d hk hd
    exact h.trans (by exact_mod_cast Nat.pos_of_ne_zero hd0)
  have herr := levelWeights_errSum_le s R hR hnu hrem
  have htotal : s.totalMass = ((X + 1 : ℕ) : ℝ) / k := rfl
  have hprime := brunTitchmarsh_primeCount_le_siftedSum X k ell R
  change (Nat.primeCountingMod X k ell : ℝ) ≤ (R + 1 : ℕ) + s.siftedSum at hprime
  change s.mainSum (BoundingSieve.lambdaSquared w) =
    1 / levelSum s R at hmain
  rw [hmain, htotal] at hsieve
  linarith

private theorem brunTitchmarsh_primeCount_le_explicit (X k ell R : ℕ)
    (hk : 0 < k) (hR : 1 ≤ R) :
    (Nat.primeCountingMod X k ell : ℝ) ≤ (R + 1 : ℕ) +
      ((X + 1 : ℕ) : ℝ) /
        ((Nat.totient k : ℝ) * Real.log (R + 1)) + (R : ℝ) ^ 12 := by
  let G := levelSum (brunTitchmarshSieve X k ell R) R
  have hbase := brunTitchmarsh_primeCount_le X k ell R hk hR
  have hG := brunTitchmarshLevelSum_ge X k ell R hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hphi : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hlog : 0 < Real.log ((R : ℝ) + 1) := by
    apply Real.log_pos
    exact_mod_cast Nat.lt_succ_of_le hR
  have hA : 0 < (Nat.totient k : ℝ) / k * Real.log (R + 1) := by
    positivity
  have hinv : 1 / G ≤
      1 / ((Nat.totient k : ℝ) / k * Real.log (R + 1)) := by
    apply one_div_le_one_div_of_le hA
    exact hG
  have hmass : 0 ≤ ((X + 1 : ℕ) : ℝ) / k := by positivity
  calc
    (Nat.primeCountingMod X k ell : ℝ) ≤ (R + 1 : ℕ) +
        ((X + 1 : ℕ) : ℝ) / k * (1 / G) + (R : ℝ) ^ 12 := hbase
    _ ≤ (R + 1 : ℕ) + ((X + 1 : ℕ) : ℝ) / k *
        (1 / ((Nat.totient k : ℝ) / k * Real.log (R + 1))) +
          (R : ℝ) ^ 12 := by
      gcongr
    _ = (R + 1 : ℕ) + ((X + 1 : ℕ) : ℝ) /
        ((Nat.totient k : ℝ) * Real.log (R + 1)) + (R : ℝ) ^ 12 := by
      field_simp

private theorem brunTitchmarsh_one_lt_div (X k : ℕ) (β : ℝ)
    (hβ1 : β < 1) (hX : 2 ≤ X) (hk : 1 ≤ k)
    (hkX : (k : ℝ) ≤ Real.rpow (X : ℝ) β) :
    1 < (X : ℝ) / k := by
  have hXR : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hpow : Real.rpow (X : ℝ) β < X := by
    calc
      Real.rpow (X : ℝ) β < Real.rpow (X : ℝ) 1 :=
        Real.rpow_lt_rpow_of_exponent_lt hXR hβ1
      _ = X := Real.rpow_one _
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [one_lt_div hkR]
  exact hkX.trans_lt hpow

private noncomputable def brunTitchmarshLevel (y : ℝ) : ℕ :=
  ⌊Real.rpow y (1 / 24 : ℝ)⌋₊

private theorem brunTitchmarshLevel_one_le {y : ℝ} (hy : 1 < y) :
    1 ≤ brunTitchmarshLevel y := by
  unfold brunTitchmarshLevel
  rw [Nat.one_le_floor_iff]
  exact Real.one_le_rpow hy.le (by norm_num)

private theorem brunTitchmarshLevel_log_lower {y : ℝ} (hy : 1 < y) :
    (1 / 24 : ℝ) * Real.log y ≤ Real.log (brunTitchmarshLevel y + 1) := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hrootpos : 0 < Real.rpow y (1 / 24 : ℝ) := Real.rpow_pos_of_pos hypos _
  have hfloor := Nat.lt_floor_add_one (Real.rpow y (1 / 24 : ℝ))
  calc
    (1 / 24 : ℝ) * Real.log y = Real.log (Real.rpow y (1 / 24 : ℝ)) :=
      (Real.log_rpow hypos _).symm
    _ ≤ Real.log ((brunTitchmarshLevel y : ℝ) + 1) :=
      (Real.log_lt_log hrootpos (by simpa only [brunTitchmarshLevel] using hfloor)).le
    _ = Real.log (brunTitchmarshLevel y + 1) := rfl

private theorem brunTitchmarshLevel_pow_twelve {y : ℝ} (hy : 1 < y) :
    (brunTitchmarshLevel y : ℝ) ^ 12 ≤ Real.rpow y (1 / 2 : ℝ) := by
  have hy0 : 0 ≤ y := (zero_lt_one.trans hy).le
  have hfloor : (brunTitchmarshLevel y : ℝ) ≤ Real.rpow y (1 / 24 : ℝ) := by
    exact Nat.floor_le (Real.rpow_nonneg hy0 _)
  calc
    (brunTitchmarshLevel y : ℝ) ^ 12 ≤
        (Real.rpow y (1 / 24 : ℝ)) ^ 12 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 12
    _ = Real.rpow y (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      calc
        Real.rpow (Real.rpow y (1 / 24 : ℝ)) (12 : ℝ) =
            Real.rpow y ((1 / 24 : ℝ) * 12) :=
          (Real.rpow_mul hy0 (1 / 24 : ℝ) 12).symm
        _ = Real.rpow y (1 / 2 : ℝ) := by norm_num

private theorem brunTitchmarshLevel_error_le {y : ℝ} (hy : 1 < y) :
    ((brunTitchmarshLevel y + 1 : ℕ) : ℝ) +
      (brunTitchmarshLevel y : ℝ) ^ 12 ≤ 6 * y / Real.log y := by
  let root := Real.rpow y (1 / 24 : ℝ)
  let sqr := Real.rpow y (1 / 2 : ℝ)
  have hypos : 0 < y := zero_lt_one.trans hy
  have hy0 : 0 ≤ y := hypos.le
  have hfloor : (brunTitchmarshLevel y : ℝ) ≤ root := by
    exact Nat.floor_le (Real.rpow_nonneg hy0 _)
  have hrootSqr : root ≤ sqr :=
    Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)
  have honeSqr : (1 : ℝ) ≤ sqr := Real.one_le_rpow hy.le (by norm_num)
  have hplus : ((brunTitchmarshLevel y + 1 : ℕ) : ℝ) ≤ 2 * sqr := by
    push_cast
    linarith
  have hpow : (brunTitchmarshLevel y : ℝ) ^ 12 ≤ sqr :=
    brunTitchmarshLevel_pow_twelve hy
  have hterms : ((brunTitchmarshLevel y + 1 : ℕ) : ℝ) +
      (brunTitchmarshLevel y : ℝ) ^ 12 ≤ 3 * sqr := by
    linarith
  have hlogpos : 0 < Real.log y := Real.log_pos hy
  have hlog : Real.log y ≤ 2 * sqr := by
    have h := Real.log_le_rpow_div hy0 (show (0 : ℝ) < 1 / 2 by norm_num)
    change Real.log y ≤ sqr / (1 / 2 : ℝ) at h
    linarith
  have hsqrSq : sqr * sqr = y := by
    change Real.rpow y (1 / 2 : ℝ) * Real.rpow y (1 / 2 : ℝ) = y
    calc
      Real.rpow y (1 / 2 : ℝ) * Real.rpow y (1 / 2 : ℝ) =
          Real.rpow y ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add hypos (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
      _ = y := by norm_num
  have hsqr : sqr ≤ 2 * y / Real.log y := by
    rw [le_div_iff₀ hlogpos]
    calc
      sqr * Real.log y ≤ sqr * (2 * sqr) := by
        exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hy0 _)
      _ = 2 * y := by rw [← hsqrSq]; ring
  calc
    ((brunTitchmarshLevel y + 1 : ℕ) : ℝ) +
        (brunTitchmarshLevel y : ℝ) ^ 12 ≤ 3 * sqr := hterms
    _ ≤ 3 * (2 * y / Real.log y) :=
      mul_le_mul_of_nonneg_left hsqr (by norm_num)
    _ = 6 * y / Real.log y := by ring

private theorem brunTitchmarsh_primeCount_le_uniform (X k ell : ℕ)
    (hk : 0 < k) (hy : 1 < (X : ℝ) / k) :
    (Nat.primeCountingMod X k ell : ℝ) ≤
      42 * (X : ℝ) /
        ((Nat.totient k : ℝ) * Real.log ((X : ℝ) / k)) := by
  let y := (X : ℝ) / k
  let R := brunTitchmarshLevel y
  have hy' : 1 < y := by simpa only [y] using hy
  have hR : 1 ≤ R := brunTitchmarshLevel_one_le hy'
  have hcount := brunTitchmarsh_primeCount_le_explicit X k ell R hk hR
  have herr := brunTitchmarshLevel_error_le hy'
  have hlog : 0 < Real.log y := Real.log_pos hy'
  have hlogR : 0 < Real.log (R + 1) := by
    apply Real.log_pos
    exact_mod_cast Nat.lt_succ_of_le hR
  have hlogLower := brunTitchmarshLevel_log_lower hy'
  have hscaledLog : 0 < (1 / 24 : ℝ) * Real.log y := by positivity
  have hinvLog : 1 / Real.log (R + 1) ≤ 24 / Real.log y := by
    calc
      1 / Real.log (R + 1) ≤
          1 / ((1 / 24 : ℝ) * Real.log y) :=
        one_div_le_one_div_of_le hscaledLog hlogLower
      _ = 24 / Real.log y := by field_simp
  have hphi : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hXreal : (2 : ℝ) ≤ X := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hyX : (k : ℝ) < X := (one_lt_div hkReal).mp hy
    have hkX : k < X := by exact_mod_cast hyX
    exact_mod_cast (show 2 ≤ X by omega)
  have hXplus : (((X + 1 : ℕ) : ℝ)) ≤ (3 / 2 : ℝ) * X := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hnum : (((X + 1 : ℕ) : ℝ)) / (Nat.totient k : ℝ) ≤
      ((3 / 2 : ℝ) * X) / (Nat.totient k : ℝ) :=
    div_le_div_of_nonneg_right hXplus hphi.le
  have hmain : (((X + 1 : ℕ) : ℝ)) /
      ((Nat.totient k : ℝ) * Real.log (R + 1)) ≤
        36 * (X : ℝ) / ((Nat.totient k : ℝ) * Real.log y) := by
    calc
      (((X + 1 : ℕ) : ℝ)) /
          ((Nat.totient k : ℝ) * Real.log (R + 1)) =
          ((((X + 1 : ℕ) : ℝ)) / (Nat.totient k : ℝ)) *
            (1 / Real.log (R + 1)) := by field_simp
      _ ≤ (((3 / 2 : ℝ) * X) / (Nat.totient k : ℝ)) *
          (24 / Real.log y) := by
        exact mul_le_mul hnum hinvLog (by positivity) (by positivity)
      _ = 36 * (X : ℝ) /
          ((Nat.totient k : ℝ) * Real.log y) := by field_simp; ring
  have hphiK : (Nat.totient k : ℝ) ≤ k := by
    exact_mod_cast Nat.totient_le k
  have hyX : y ≤ (X : ℝ) / Nat.totient k := by
    dsimp only [y]
    exact div_le_div_of_nonneg_left (by positivity) hphi hphiK
  have herr' : ((R + 1 : ℕ) : ℝ) + (R : ℝ) ^ 12 ≤
      6 * (X : ℝ) /
        ((Nat.totient k : ℝ) * Real.log y) := by
    calc
      ((R + 1 : ℕ) : ℝ) + (R : ℝ) ^ 12 ≤
          6 * y / Real.log y := herr
      _ ≤ 6 * ((X : ℝ) / Nat.totient k) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hlog.le
        exact mul_le_mul_of_nonneg_left hyX (by norm_num)
      _ = 6 * (X : ℝ) /
          ((Nat.totient k : ℝ) * Real.log y) := by field_simp
  change (Nat.primeCountingMod X k ell : ℝ) ≤
    42 * (X : ℝ) / ((Nat.totient k : ℝ) * Real.log y)
  calc
    (Nat.primeCountingMod X k ell : ℝ) ≤
        ((R + 1 : ℕ) : ℝ) +
          (((X + 1 : ℕ) : ℝ)) /
            ((Nat.totient k : ℝ) * Real.log (R + 1)) +
          (R : ℝ) ^ 12 := hcount
    _ = (((R + 1 : ℕ) : ℝ) + (R : ℝ) ^ 12) +
        (((X + 1 : ℕ) : ℝ)) /
          ((Nat.totient k : ℝ) * Real.log (R + 1)) := by ring
    _ ≤ 6 * (X : ℝ) / ((Nat.totient k : ℝ) * Real.log y) +
        36 * (X : ℝ) / ((Nat.totient k : ℝ) * Real.log y) :=
      add_le_add herr' hmain
    _ = 42 * (X : ℝ) /
        ((Nat.totient k : ℝ) * Real.log y) := by ring

/-- **Uniform Brun–Titchmarsh bound.** Write $\pi(X; k, \ell)$ for the number of primes $p \le X$
with $p \equiv \ell \pmod{k}$, and $\varphi$ for Euler's totient function. For every real $\beta$
with $0 < \beta < 1$ there is a real constant $\xi_1 > 0$ such that for all natural numbers $X$,
$k$ and $\ell$ with $X \ge 2$, $k \ge 1$ and $k \le X^{\beta}$,
$$
\pi(X; k, \ell) < \frac{\xi_1 X}{\varphi(k) \log(X/k)}.
$$

No coprimality of $k$ and $\ell$ is assumed.

The proof applies Selberg's $\Lambda^2$ upper-bound sieve to the arithmetic progression, with
optimized weights and a harmonic lower bound for the diagonal sum.

Proves `Wanted` entry `brun_titchmarsh_uniform`.

Source: Jean-Marie De Koninck and Imre Kátai, "Some Remarks on a Paper of
L. Toth," Journal of Integer Sequences 13 (2010),
`https://cs.uwaterloo.ca/journals/JIS/VOL13/DeKoninck/dekoninck7.tex`,
Lemma `lem:pi`, lines 424–429. Both the live and bundled source have SHA-256
`a81e23b6e88f02c8bcad5f1b6e4d71d822e82e1725a9e8ba2708bd2bc0e4a57d`, and the
exact lines 424–429 joined by LF without a terminal LF have SHA-256
`bd645263ac19a24bf1b4ff3ac5baf13ec5ee8f59ae16945edd528cf4ac153828`. The source
cites E. C. Titchmarsh, "A divisor problem," Rend. Palermo 54 (1930), 414–429
and 57 (1933), 478–479. The bound `2 ≤ X` makes the source's implicit analytic
lower range explicit, and the source prints no coprimality hypothesis.
-/
public theorem brun_titchmarsh_uniform (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    ∃ ξ₁ : ℝ, 0 < ξ₁ ∧ ∀ X k ell : ℕ, 2 ≤ X → 1 ≤ k →
      (k : ℝ) ≤ Real.rpow (X : ℝ) β →
      (Nat.primeCountingMod X k ell : ℝ) <
        ξ₁ * (X : ℝ) / ((Nat.totient k : ℝ) * Real.log ((X : ℝ) / (k : ℝ))) := by
  refine ⟨43, by norm_num, ?_⟩
  intro X k ell hX hk hkX
  have hkpos : 0 < k := by omega
  have hy := brunTitchmarsh_one_lt_div X k β hβ1 hX hk hkX
  have hbound := brunTitchmarsh_primeCount_le_uniform X k ell hkpos hy
  have hphi : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.mpr hkpos
  have hlog : 0 < Real.log ((X : ℝ) / k) := Real.log_pos hy
  have hden : 0 < (Nat.totient k : ℝ) * Real.log ((X : ℝ) / k) :=
    mul_pos hphi hlog
  calc
    (Nat.primeCountingMod X k ell : ℝ) ≤
        42 * (X : ℝ) /
          ((Nat.totient k : ℝ) * Real.log ((X : ℝ) / k)) := hbound
    _ < 43 * (X : ℝ) /
        ((Nat.totient k : ℝ) * Real.log ((X : ℝ) / k)) := by
      apply (div_lt_div_iff_of_pos_right hden).2
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
      nlinarith

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
