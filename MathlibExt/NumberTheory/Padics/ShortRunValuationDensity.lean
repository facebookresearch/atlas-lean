/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PadicValNat
public import MathlibExt.Data.Set.Density
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-!
# Valuations on logarithmically short runs

The starting integers for which all logarithmically short runs satisfy the prime valuation
bound have natural density one.
-/

namespace MetaMathlibExt

open Filter Finset Real Topology

namespace max_padicValNat_add_le_density_one

private def Good (m : ℕ) : Prop :=
  ∀ k : ℕ, log m / 2 < k → (k : ℝ) < log m → ∀ p : ℕ, p.Prime → p ≤ 2 * k →
    (((Icc 1 k).sup fun i => padicValNat p (m + i) : ℕ) : ℝ) ≤ 3 * log k / log p

private noncomputable def scale (x : ℕ) : ℕ := ⌈log x / 4⌉₊

-- Beyond √x, every relevant run length lies between K and 4K.
private lemma run_bounds {m k x : ℕ} (hx : 0 < x) (hm : √(x : ℝ) ≤ m) (hmx : m < x)
    (hlo : log m / 2 < k) (hhi : (k : ℝ) < log m) : scale x ≤ k ∧ k ≤ 4 * scale x := by
  have hroot := sqrt_pos.mpr (Nat.cast_pos.mpr hx)
  have hl := log_le_log hroot hm
  rw [log_sqrt (Nat.cast_nonneg _)] at hl
  have hu := log_le_log (hroot.trans_le hm) (Nat.cast_le.mpr hmx.le)
  refine ⟨Nat.ceil_le.mpr (by linarith), ?_⟩
  have hK : log x / 4 ≤ (scale x : ℝ) := Nat.le_ceil _
  exact_mod_cast (show (k : ℝ) ≤ 4 * (scale x : ℝ) by linarith)

-- A large valuation forces divisibility by the first power of p at least K³.
private lemma large_power_dvd {K k p n : ℕ} (hK : 0 < K) (hk : K ≤ k) (hp : p.Prime)
    (hv : 3 * log k / log p < (padicValNat p n : ℝ)) : p ^ Nat.clog p (K ^ 3) ∣ n := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hk' : (0 : ℝ) < k := by exact_mod_cast hK.trans_le hk
  have hlog := (div_lt_iff₀ (log_pos hp')).mp hv
  have hpow : k ^ 3 ≤ p ^ padicValNat p n := by
    exact_mod_cast (show (k : ℝ) ^ 3 ≤ (p : ℝ) ^ padicValNat p n by
      apply (log_le_log_iff (by positivity) (by positivity)).mp
      rw [log_pow, log_pow]
      exact hlog.le)
  have he := Nat.clog_le_of_le_pow ((Nat.pow_le_pow_left hk 3).trans hpow)
  rw [Nat.padicValNat_def] at he
  exact (pow_dvd_pow p he).trans (pow_multiplicity_dvd ..)

private lemma exceptional_card_le (x : ℕ) (hx : 0 < x) (hK : 0 < scale x) :
    open scoped Classical in
    ((range x).filter fun m => ¬ Good m).card ≤
      ⌊√(x : ℝ)⌋₊ + 1 + (8 * scale x) * (4 * scale x) * ((x + 4 * scale x) / scale x ^ 3) := by
  classical
  let K := scale x
  let primes := (Icc 1 (8 * K)).filter Nat.Prime
  let shifts := Icc 1 (4 * K)
  let multiples (p : ℕ) := (Ioc 0 (x + 4 * K)).filter (p ^ Nat.clog p (K ^ 3) ∣ ·)
  let starts (p i : ℕ) := (multiples p).image (fun n => n - i)
  let small := Iic ⌊√(x : ℝ)⌋₊
  have hcover : ((range x).filter fun m => ¬ Good m) ⊆
      small ∪ primes.biUnion (fun p => shifts.biUnion (starts p)) := by
    intro m hm
    obtain ⟨hmx, hbad⟩ := mem_filter.mp hm
    have hmx' := mem_range.mp hmx
    by_cases hm : (m : ℝ) ≤ √(x : ℝ)
    · exact mem_union_left _ (mem_Iic.mpr (Nat.le_floor hm))
    unfold Good at hbad
    push Not at hbad
    obtain ⟨k, hlo, hhi, p, hp, hpk, hv⟩ := hbad
    obtain ⟨hKk, hkK⟩ := run_bounds hx (le_of_not_ge hm) hmx' hlo hhi
    obtain ⟨i, hi, heq⟩ := exists_mem_eq_sup (Icc 1 k) (nonempty_Icc.mpr (hK.trans_le hKk))
      (fun i => padicValNat p (m + i))
    rw [heq] at hv
    obtain ⟨hi₁, hik⟩ := mem_Icc.mp hi
    have hiK : i ≤ 4 * K := hik.trans hkK
    have hpK : p ≤ 8 * K := by change k ≤ 4 * K at hkK; omega
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hp.pos, hpK⟩, hp⟩, mem_biUnion.mpr ⟨i, mem_Icc.mpr ⟨hi₁, hiK⟩, ?_⟩⟩)
    exact mem_image.mpr ⟨m + i, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩,
      large_power_dvd hK hKk hp hv⟩, Nat.add_sub_cancel ..⟩
  have hcount (p : ℕ) (hp : p ∈ primes) :
      (shifts.biUnion (starts p)).card ≤ 4 * K * ((x + 4 * K) / K ^ 3) := by
    simpa [shifts] using card_biUnion_le_card_mul shifts (starts p) ((x + 4 * K) / K ^ 3) (by
      intro i _
      calc
        (starts p i).card ≤ (multiples p).card := card_image_le
        _ = (x + 4 * K) / p ^ Nat.clog p (K ^ 3) := Nat.Ioc_filter_dvd_card_eq_div ..
        _ ≤ _ := Nat.div_le_div_left (Nat.le_pow_clog (mem_filter.mp hp).2.one_lt _) (pow_pos hK 3))
  have hprimes : primes.card ≤ 8 * K := (card_filter_le ..).trans_eq (by simp)
  calc
    _ ≤ _ := (card_le_card hcover).trans (card_union_le ..)
    _ ≤ small.card + primes.card * (4 * K * ((x + 4 * K) / K ^ 3)) :=
      Nat.add_le_add_left (card_biUnion_le_card_mul _ _ _ hcount) _
    _ ≤ small.card + (8 * K) * (4 * K * ((x + 4 * K) / K ^ 3)) := by gcongr
    _ = _ := by simp [small, K, Nat.mul_assoc]

open scoped Classical in
private lemma exceptional_proportion :
    Tendsto (fun x : ℕ => (((range x).filter fun m => ¬ Good m).card : ℝ) / x) atTop (𝓝 0) := by
  classical
  have hscale : Tendsto scale atTop atTop := tendsto_nat_ceil_atTop.comp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 4))
  have hsqrt : Tendsto (fun x : ℕ => √(x : ℝ) / x) atTop (𝓝 0) := by
    simpa only [sqrt_div_self, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hrare : Tendsto (fun x : ℕ => 96 / (scale x : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 96 |>.comp hscale
  have hlim := (hsqrt.add tendsto_one_div_atTop_nhds_zero_nat).add hrare
  simp only [add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 4, hscale.eventually_ge_atTop 1] with x hx hK
  let K := scale x
  have hx' : (4 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : 0 < (x : ℝ) := by linarith
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
  have hwidth : 4 * K ≤ 2 * x := by
    have hceil := Nat.ceil_lt_add_one (div_nonneg (log_nonneg (by linarith : 1 ≤ (x : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 4))
    exact_mod_cast (show 4 * (K : ℝ) ≤ 2 * x by
      change (K : ℝ) < log x / 4 + 1 at hceil
      linarith [log_le_self hxpos.le])
  let B := (8 * K) * (4 * K) * ((x + 4 * K) / K ^ 3)
  have hB : B * K ≤ 96 * x := calc
    _ = 32 * (((x + 4 * K) / K ^ 3) * K ^ 3) := by dsimp [B]; ring
    _ ≤ 32 * (x + 4 * K) := Nat.mul_le_mul_left 32 (Nat.div_mul_le_self ..)
    _ ≤ _ := by omega
  have hratio : (B : ℝ) / x ≤ 96 / K :=
    (div_le_div_iff₀ hxpos hKpos).mpr (by exact_mod_cast hB)
  have hc := exceptional_card_le x (by omega) hK
  change _ ≤ ⌊√(x : ℝ)⌋₊ + 1 + B at hc
  calc
    _ ≤ ((⌊√(x : ℝ)⌋₊ : ℝ) + 1 + B) / x :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) hxpos.le
    _ ≤ (√(x : ℝ) / x + 1 / x) + 96 / K := by
      rw [add_div, add_div]
      gcongr
      exact Nat.floor_le (sqrt_nonneg _)

end max_padicValNat_add_le_density_one

open max_padicValNat_add_le_density_one in
/-- **Short runs of consecutive integers have small valuations almost always.** Write $v_p(n)$
for the exponent of a prime $p$ in a positive integer $n$. The set of natural numbers $m$ such
that $\max \{ v_p(m + i) : 1 \le i \le k \} \le 3 \log k / \log p$ for every integer $k$ with
$\frac{1}{2} \log m < k < \log m$ and every prime $p \le 2k$ has natural density $1$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 2 (`integers-2026-A47-lem-2`). -/
public theorem max_padicValNat_add_le_density_one :
    ({m : ℕ | ∀ k : ℕ, Real.log m / 2 < k → (k : ℝ) < Real.log m → ∀ p : ℕ, p.Prime →
        p ≤ 2 * k →
          (((Finset.Icc 1 k).sup fun i => padicValNat p (m + i) : ℕ) : ℝ) ≤
            3 * Real.log k / Real.log p} : Set ℕ).HasDensity 1 := by
  classical
  change {m : ℕ | Good m}.HasDensity 1
  simp only [Set.HasDensity, Set.partialDensity, Set.univ_inter, Set.inter_univ, Set.ncard_Iio_nat]
  have h := tendsto_const_nhds.sub exceptional_proportion (a := (1 : ℝ))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hset : {m | Good m} ∩ Set.Iio x = ↑((range x).filter Good) := by
    ext m
    simp [and_comm]
  rw [hset, Set.ncard_coe_finset]
  have htotal := card_filter_add_card_filter_not (s := range x) Good
  rw [card_range] at htotal
  have hxpos : (x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  rw [sub_eq_iff_eq_add]
  exact_mod_cast htotal.symm

end MetaMathlibExt
