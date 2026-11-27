/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import MathlibExt.NumberTheory.IncompleteExponentialSum
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Bounds for sums of reciprocal sines

We prove two of Cochrane's bounds for a sum of reciprocal absolute sines modulo a prime: the
plain sum, `MetaMathlibExt.sum_one_div_abs_sin_lt`, and the sum with each term capped at the
length `B`, `MetaMathlibExt.sum_min_one_div_abs_sin_lt`. Both proofs order the distinct least
absolute residues, through one comparison lemma for a monotone function of the reciprocal
values, and apply the same pointwise cosecant bound. For the capped sum, the harmonic part is
split at `⌊p/(πB)⌋₊` and bounded with Mathlib's estimates for harmonic numbers.
-/

namespace MetaMathlibExt

open Finset

namespace sum_one_div_abs_sin_lt

open Filter

/-- The harmonic number differs from `log n + γ` by at most `1 / (2 * n)` on the upper side. -/
private lemma harmonic_le_log_add_gamma (n : ℕ) (hn : 0 < n) :
    (harmonic n : ℝ) ≤ Real.log n + Real.eulerMascheroniConstant + 1 / (2 * n) := by
  let u (k : ℕ) : ℝ :=
    (harmonic (k + 1) : ℝ) - Real.log (↑(k + 1 : ℕ)) - 1 / (2 * ↑(k + 1 : ℕ))
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro k
    let x : ℝ := (k : ℝ) + 1
    have hx : 0 < x := by dsimp [x]; positivity
    have hx₁ : 0 < x + 1 := by positivity
    have hratio : 1 ≤ (x + 1) / x := (le_div_iff₀ hx).2 (by linarith)
    have hlog := Real.self_le_sinh_iff.mpr (Real.log_nonneg hratio)
    rw [Real.sinh_log (by positivity), Real.log_div hx₁.ne' hx.ne'] at hlog
    have hidentity : ((x + 1) / x - ((x + 1) / x)⁻¹) / 2 =
        1 / (2 * x) + 1 / (2 * (x + 1)) := by
      field_simp
      ring
    rw [hidentity] at hlog
    have hhalf : 1 / (x + 1) = 1 / (2 * (x + 1)) + 1 / (2 * (x + 1)) := by
      field_simp
      ring
    dsimp only [u]
    rw [harmonic_succ (k + 1)]
    push_cast
    change (harmonic (k + 1) : ℝ) - Real.log x - 1 / (2 * x) ≤
      (harmonic (k + 1) : ℝ) + (x + 1)⁻¹ - Real.log (x + 1) - 1 / (2 * (x + 1))
    rw [← one_div, hhalf]
    linarith
  have hlim : Tendsto u atTop (nhds Real.eulerMascheroniConstant) := by
    have hmain := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto (fun k : ℕ ↦ (1 / (2 * ((k : ℝ) + 1)) : ℝ))
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)⁻¹)
    simpa [u, Function.comp_def, Nat.cast_add, Nat.cast_one] using hmain.sub hinv
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h : (harmonic n : ℝ) - Real.log n - 1 / (2 * n) ≤ Real.eulerMascheroniConstant := by
    simpa only [u, hn'] using hu.ge_of_tendsto hlim (n - 1)
  linarith only [h]

/-- Absolute sine with argument `π x / p` only depends on the residue of the integer `x`. -/
private lemma abs_sin_eq_of_zmod_eq {p : ℕ} (hp : 0 < p) {x y : ℤ}
    (h : (x : ZMod p) = y) :
    |Real.sin (Real.pi * x / p)| = |Real.sin (Real.pi * y / p)| := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mp h
  have hxy : (y : ℝ) - x = p * (k : ℝ) := by exact_mod_cast hk
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have harg : Real.pi * y / p = Real.pi * x / p + (k : ℝ) * Real.pi := by
    field_simp
    linear_combination hxy
  rw [harg, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]

/-- Sorting the least absolute residues of `a h` bounds the sum of `g (1 / |sin (π a h / p)|)`
by the case `a = 1`, for every monotone `g`. -/
private lemma sum_le_unmultiplied (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB : 2 * B < p) (g : ℝ → ℝ) (hg : Monotone g) :
    ∑ h ∈ Icc 1 B, g (1 / |Real.sin (Real.pi * a * h / p)|) ≤
      ∑ j ∈ Icc 1 B, g (1 / Real.sin (Real.pi * j / p)) := by
  let : Fact p.Prime := ⟨hp⟩
  let z (h : ℕ) : ZMod p := (a : ZMod p) * (h : ZMod p)
  let r (h : ℕ) : ℕ := (z h).valMinAbs.natAbs
  have ha' : (a : ZMod p) ≠ 0 := fun h ↦ ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 h)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpi := Real.pi_pos
  have hr (h : ℕ) (hh : h ∈ Icc 1 B) : 0 < r h ∧ r h ≤ p / 2 := by
    obtain ⟨hh₁, hhB⟩ := mem_Icc.mp hh
    refine ⟨Nat.pos_of_ne_zero ?_, (z h).natAbs_valMinAbs_le⟩
    intro hz
    have hhzero : (h : ZMod p) = 0 := (mul_eq_zero.mp
      ((z h).valMinAbs_eq_zero.mp (Int.natAbs_eq_zero.mp hz))).resolve_left ha'
    have hval := congrArg ZMod.val hhzero
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
    omega
  have hrinj : Set.InjOn r (↑(Icc 1 B) : Set ℕ) := by
    intro i hi j hj hij
    obtain ⟨hi₁, hiB⟩ := mem_Icc.mp (mem_coe.mp hi)
    obtain ⟨hj₁, hjB⟩ := mem_Icc.mp (mem_coe.mp hj)
    rcases ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp hij with h | h
    · have hval := congrArg ZMod.val (mul_left_cancel₀ ha' h)
      simpa only [ZMod.val_natCast_of_lt (show i < p by omega),
        ZMod.val_natCast_of_lt (show j < p by omega)] using hval
    · have hneg : (i : ZMod p) = -(j : ZMod p) :=
        mul_left_cancel₀ ha' (by simpa only [mul_neg] using h)
      have hzero : ((i + j : ℕ) : ZMod p) = 0 := by simp [hneg]
      have hval := congrArg ZMod.val hzero
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
      omega
  let f (j : ℕ) := g (1 / Real.sin (Real.pi * j / p))
  have harg (j : ℕ) (hj : j ≤ p / 2) : Real.pi * j / p ≤ Real.pi / 2 := by
    have hj' : (j : ℝ) * 2 ≤ p := by exact_mod_cast Nat.le_div_two_iff_mul_two_le.mp hj
    rw [div_le_iff₀ hp']
    nlinarith [mul_le_mul_of_nonneg_left hj' hpi.le]
  have hterm (h : ℕ) (hh : h ∈ Icc 1 B) :
      g (1 / |Real.sin (Real.pi * a * h / p)|) = f (r h) := by
    have hcast : ((a * (h : ℤ) : ℤ) : ZMod p) = (z h).valMinAbs := by simp [z]
    have hsin := abs_sin_eq_of_zmod_eq hp.pos hcast
    push_cast at hsin
    rw [← mul_assoc] at hsin
    have habs : |Real.pi * ((z h).valMinAbs : ℝ) / p| = Real.pi * (r h : ℝ) / p := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hp', ← Int.cast_abs, Int.abs_eq_natAbs]
      rfl
    rw [hsin, Real.abs_sin_eq_sin_abs_of_abs_le_pi, habs]
    exact (habs.trans_le (harg _ (hr h hh).2)).trans (by linarith)
  have hsin_anti {i j : ℕ} (hi : i ∈ Set.Icc 1 (p / 2)) (hj : j ∈ Set.Icc 1 (p / 2))
      (hij : i ≤ j) :
      1 / Real.sin (Real.pi * j / p) ≤ 1 / Real.sin (Real.pi * i / p) := by
    have hi₀ : (0 : ℝ) < i := by exact_mod_cast (show 0 < i from hi.1)
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    apply one_div_le_one_div_of_le
    · exact Real.sin_pos_of_pos_of_lt_pi (by positivity) ((harg i hi.2).trans_lt (by linarith))
    · have hz : (0 : ℝ) ≤ Real.pi * i / p := by positivity
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (harg j hj.2) (by gcongr)
  have hf : AntitoneOn f (Set.Icc 1 (p / 2)) := by
    intro i hi j hj hij
    exact hg (hsin_anti hi hj hij)
  let s := (Icc 1 B).image r
  have hs : s.card = B := by rw [card_image_of_injOn hrinj]; simp
  let e := s.orderEmbOfFin hs
  have he (i : Fin B) : 0 < e i ∧ e i ≤ p / 2 := by
    obtain ⟨h, hh, heq⟩ := mem_image.mp (s.orderEmbOfFin_mem hs i)
    simpa only [e, ← heq] using hr h hh
  have hindex (i : Fin B) : (i : ℕ) + 1 ≤ e i := by
    have hcard := card_le_card_of_injOn (s := Iic i) (t := Icc 1 (e i)) e
      (fun j hj ↦ mem_coe.mpr (mem_Icc.mpr
        ⟨(he j).1, e.monotone (mem_Iic.mp (mem_coe.mp hj))⟩)) e.injective.injOn
    simpa only [Fin.card_Iic, Nat.card_Icc, Nat.add_sub_cancel] using hcard
  have hIcc : (Icc 1 B).card = B := by simp
  have hshift : ((Icc 1 B).orderEmbOfFin hIcc : Fin B → ℕ) = fun (i : Fin B) ↦ (i : ℕ) + 1 :=
    (orderEmbOfFin_unique hIcc (fun i ↦ mem_Icc.mpr ⟨by omega, i.isLt⟩)
      (fun _ _ hij ↦ Nat.add_lt_add_right hij 1)).symm
  calc
    _ = ∑ j ∈ s, f j := by
      rw [sum_image hrinj]
      exact sum_congr rfl hterm
    _ = ∑ i : Fin B, f (e i) := by
      rw [← s.map_orderEmbOfFin_univ hs, sum_map]
      rfl
    _ ≤ ∑ i : Fin B, f ((i : ℕ) + 1) := by
      apply sum_le_sum
      intro i _
      exact hf ⟨by omega, (hindex i).trans (he i).2⟩ (he i) (hindex i)
    _ = ∑ j ∈ Icc 1 B, f j := by
      rw [← (Icc 1 B).map_orderEmbOfFin_univ hIcc, sum_map]
      exact sum_congr rfl fun i _ ↦ (congrArg f (congrFun hshift i)).symm

/-- Pointwise bound for `1 / sin (π j / p)` from the partial-fraction estimate. -/
private lemma one_div_sin_lt (p B j : ℕ) (hp : p.Prime) (hB : (B : ℝ) < p)
    (hj₁ : 1 ≤ j) (hjB : j ≤ B) :
    1 / Real.sin (Real.pi * j / p) <
      (p / Real.pi) * (j : ℝ)⁻¹ + (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j from hj₁)
  have hjB' : (j : ℝ) ≤ B := by exact_mod_cast hjB
  have hjp : (j : ℝ) < p := hjB'.trans_lt hB
  have hjsq : 0 < (p : ℝ) ^ 2 - (j : ℝ) ^ 2 := by
    apply sub_pos.mpr
    gcongr
  have hBsq : 0 < (p : ℝ) ^ 2 - (B : ℝ) ^ 2 := by
    apply sub_pos.mpr
    gcongr
  calc
    _ < (1 / Real.pi) * (1 / ((j : ℝ) / p) +
        2 * ((j : ℝ) / p) / (1 - ((j : ℝ) / p) ^ 2)) := by
      rw [mul_div_assoc]
      exact one_div_sin_pi_lt _ (by positivity) ((div_lt_one hp').mpr hjp)
    _ = (p / Real.pi) * (j : ℝ)⁻¹ +
        (2 * p / (Real.pi * ((p : ℝ) ^ 2 - (j : ℝ) ^ 2))) * j := by
      have : 1 - ((j : ℝ) / p) ^ 2 ≠ 0 := by
        rw [div_pow, sub_ne_zero]
        exact ((div_lt_one (by positivity)).mpr (sub_pos.mp hjsq)).ne'
      field_simp
    _ ≤ _ := by gcongr

/-- The sum `1 + ⋯ + n`, as a real number. -/
private lemma sum_Icc_natCast (n : ℕ) : ∑ j ∈ Icc 1 n, (j : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

end sum_one_div_abs_sin_lt

/-- **Bound for a sum of reciprocal sines.** Let $p$ be a prime, let $a$ be an integer not
divisible by $p$, let $B$ be an integer with $1 \le B < p/2$, and let $\gamma$ be the
Euler–Mascheroni constant. Then
$$
\sum_{h=1}^{B} \frac{1}{|\sin(\pi a h / p)|} <
\frac{p}{\pi}\left(\log B + \gamma + \frac{1}{2B}\right) + \frac{pB(B+1)}{\pi(p^2 - B^2)}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.2 (`integers-2025-A48-lem-3-2`). -/
public theorem sum_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : 1 ≤ B) (hB : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, 1 / |Real.sin (Real.pi * a * h / p)| <
      (p / Real.pi) * (Real.log B + Real.eulerMascheroniConstant + 1 / (2 * B)) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpπ : 0 < (p : ℝ) / Real.pi := by positivity
  have hB' : (B : ℝ) < p := by linarith
  have hB₂ : 2 * B < p := by exact_mod_cast (show 2 * (B : ℝ) < p by linarith)
  calc
    _ ≤ ∑ j ∈ Icc 1 B, 1 / Real.sin (Real.pi * j / p) :=
      sum_one_div_abs_sin_lt.sum_le_unmultiplied p hp a ha B hB₂ id monotone_id
    _ < ∑ j ∈ Icc 1 B,
        ((p / Real.pi) * (j : ℝ)⁻¹ + (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j) :=
      sum_lt_sum_of_nonempty (nonempty_Icc.mpr hB₁) fun j hj ↦
        sum_one_div_abs_sin_lt.one_div_sin_lt p B j hp hB' (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
    _ = (p / Real.pi) * (harmonic B : ℝ) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
      simp only [sum_add_distrib, ← mul_sum, sum_one_div_abs_sin_lt.sum_Icc_natCast,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sum_one_div_abs_sin_lt.harmonic_le_log_add_gamma B hB₁) hpπ.le)
      le_rfl

namespace sum_min_one_div_abs_sin_lt

/-- A minimum against a sum splits off the nonnegative error term. -/
private lemma min_add_le (B X Y e : ℝ) (he : 0 ≤ e) (h : X ≤ Y + e) :
    min B X ≤ min B Y + e := by
  rcases le_or_gt X B with hX | hX
  · rcases le_or_gt Y B with hY | hY
    · rw [min_eq_right hX, min_eq_right hY]
      exact h
    · rw [min_eq_right hX, min_eq_left hY.le]
      linarith
  · rcases le_or_gt Y B with hY | hY
    · rw [min_eq_left hX.le, min_eq_right hY]
      linarith
    · rw [min_eq_left hX.le, min_eq_left hY.le]
      linarith


/-- The reciprocals of `m + 1, …, B` sum to the difference of harmonic numbers. -/
private lemma sum_Icc_succ_inv (m B : ℕ) (hmB : m ≤ B) :
    ∑ j ∈ Icc (m + 1) B, (j : ℝ)⁻¹ = (harmonic B : ℝ) - harmonic m := by
  have hsplit : (Icc 1 B : Finset ℕ) = Icc 1 m ∪ Icc (m + 1) B := by
    ext j
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 m) (Icc (m + 1) B) := by
    rw [disjoint_left]
    intro j hj1 hj2
    simp only [mem_Icc] at hj1 hj2
    omega
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc, hsplit, sum_union hdisj]
  push_cast
  ring

/-- Splitting the truncated sum at `m` gives the capped part plus a harmonic tail. -/
private lemma main_sum_split (p B m : ℕ) (hp : p.Prime) (hB0 : 0 < B) (hmB : m < B)
    (hmT : (m : ℝ) ≤ (p : ℝ) / (Real.pi * B)) (hTm : (p : ℝ) / (Real.pi * B) < m + 1) :
    ∑ j ∈ Icc 1 B, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) =
      B * m + (p / Real.pi) * ∑ j ∈ Icc (m + 1) B, (j : ℝ)⁻¹ := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpi := Real.pi_pos
  have hB0' : (0 : ℝ) < B := by exact_mod_cast hB0
  have hT0 : (0 : ℝ) < (p : ℝ) / (Real.pi * B) := by positivity
  have hT0' : (p : ℝ) / (Real.pi * B) ≠ 0 := ne_of_gt hT0
  have hTT : ((p : ℝ) / (Real.pi * B)) * ((p : ℝ) / (Real.pi * B))⁻¹ = 1 :=
    mul_inv_cancel₀ hT0'
  have hcT : (B : ℝ) * ((p : ℝ) / (Real.pi * B)) = p / Real.pi := by
    have hB0'' : (B : ℝ) ≠ 0 := ne_of_gt hB0'
    have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
    field_simp
  have hsplit : (Icc 1 B : Finset ℕ) = Icc 1 m ∪ Icc (m + 1) B := by
    ext j
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 m) (Icc (m + 1) B) := by
    rw [disjoint_left]
    intro j hj1 hj2
    simp only [mem_Icc] at hj1 hj2
    omega
  have hcap : ∀ j ∈ Icc 1 m, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) = B := by
    intro j hj
    obtain ⟨hj1, hjm⟩ := mem_Icc.mp hj
    apply min_eq_left
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hjmT : (j : ℝ) ≤ (p : ℝ) / (Real.pi * B) :=
      ((by exact_mod_cast hjm : (j : ℝ) ≤ (m : ℝ))).trans hmT
    have h1 : ((p : ℝ) / (Real.pi * B))⁻¹ ≤ (j : ℝ)⁻¹ := by
      have h := one_div_le_one_div_of_le hj0 hjmT
      rwa [one_div, one_div] at h
    calc (B : ℝ) = (B : ℝ) * (((p : ℝ) / (Real.pi * B)) * ((p : ℝ) / (Real.pi * B))⁻¹) := by
            rw [hTT, mul_one]
          _ ≤ (B : ℝ) * (((p : ℝ) / (Real.pi * B)) * (j : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hT0.le) hB0'.le
          _ = (p / Real.pi) * (j : ℝ)⁻¹ := by rw [← hcT]; ring
  have htail : ∀ j ∈ Icc (m + 1) B, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) =
      (p / Real.pi) * (j : ℝ)⁻¹ := by
    intro j hj
    obtain ⟨hj1, -⟩ := mem_Icc.mp hj
    apply min_eq_right
    have hjT : (p : ℝ) / (Real.pi * B) < (j : ℝ) :=
      lt_of_lt_of_le hTm (by exact_mod_cast hj1)
    have h1 : (j : ℝ)⁻¹ < ((p : ℝ) / (Real.pi * B))⁻¹ := by
      have h := one_div_lt_one_div_of_lt hT0 hjT
      rwa [one_div, one_div] at h
    have hlt : (p / Real.pi) * (j : ℝ)⁻¹ < B := by
      calc (p / Real.pi) * (j : ℝ)⁻¹
            = (B : ℝ) * (((p : ℝ) / (Real.pi * B)) * (j : ℝ)⁻¹) := by rw [← hcT]; ring
          _ < (B : ℝ) * (((p : ℝ) / (Real.pi * B)) * (((p : ℝ) / (Real.pi * B))⁻¹)) :=
            mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h1 hT0) hB0'
          _ = B := by rw [hTT, mul_one]
    exact hlt.le
  have hcard : m + 1 - 1 = m := by omega
  rw [hsplit, sum_union hdisj, sum_congr rfl hcap, sum_congr rfl htail, sum_const,
    Nat.card_Icc, nsmul_eq_mul, hcard, ← mul_sum]
  ring

/-- The unmultiplied truncated sum is less than the logarithmic main term. -/
private lemma main_sum_lt (p B : ℕ) (hp : p.Prime) (hB₁ : Real.sqrt (p / Real.pi) < B) :
    ∑ j ∈ Icc 1 B, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) <
      (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpi := Real.pi_pos
  have hB0 : (0 : ℝ) < B := lt_of_le_of_lt (Real.sqrt_nonneg _) hB₁
  have hB0n : 0 < B := Nat.cast_pos.mp hB0
  have hB1 : 1 ≤ B := hB0n
  have hc : (0 : ℝ) < p / Real.pi := by positivity
  have hT0 : (0 : ℝ) < (p : ℝ) / (Real.pi * B) := by positivity
  have hsq : (p : ℝ) / Real.pi < (B : ℝ) ^ 2 := by
    have h := (Real.sqrt_lt' hB0).mp hB₁
    simpa using h
  have hTB : (p : ℝ) / (Real.pi * B) < B := by
    have h1 : (p : ℝ) < Real.pi * B ^ 2 := by
      have h2 := (div_lt_iff₀ hpi).mp hsq
      linear_combination h2
    rw [div_lt_iff₀ (by positivity)]
    have h3 : (B : ℝ) * (Real.pi * B) = Real.pi * B ^ 2 := by ring
    rw [h3]
    exact h1
  have hmT : ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) ≤ (p : ℝ) / (Real.pi * B) :=
    Nat.floor_le hT0.le
  have hTm : (p : ℝ) / (Real.pi * B) < ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hmB : ⌊(p : ℝ) / (Real.pi * B)⌋₊ < B :=
    Nat.cast_lt.mp (lt_of_le_of_lt hmT hTB)
  have hsplit :=
    main_sum_split p B ⌊(p : ℝ) / (Real.pi * B)⌋₊ hp hB0n hmB hmT hTm
  rcases Nat.eq_zero_or_pos ⌊(p : ℝ) / (Real.pi * B)⌋₊ with hm0 | hm0
  · have hT1 : (p : ℝ) / (Real.pi * B) < 1 := by
      have h := hTm
      rw [hm0] at h
      simpa using h
    rw [hm0] at hsplit
    simp only [Nat.cast_zero, mul_zero, zero_add] at hsplit
    have hH : ∑ j ∈ Icc 1 B, (j : ℝ)⁻¹ ≤ 1 + Real.log B := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
        harmonic_le_one_add_log B
    have hpos : (0 : ℝ) < Real.pi * B / p := div_pos (mul_pos hpi hB0) hp'
    have hBπ : (1 : ℝ) < Real.pi * B / p := by
      rw [lt_div_iff₀ hp']
      have h := (div_lt_iff₀ (show (0 : ℝ) < Real.pi * B by positivity)).mp hT1
      simpa using h
    have hlog : (0 : ℝ) < Real.log (Real.pi * B / p) := Real.log_pos hBπ
    have hdecomp : Real.log (Real.pi * B ^ 2 / p) = Real.log B + Real.log (Real.pi * B / p) := by
      have heq : Real.pi * B ^ 2 / p = B * (Real.pi * B / p) := by
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp'
        field_simp
      rw [heq, Real.log_mul (ne_of_gt hB0) (ne_of_gt hpos)]
    rw [hsplit]
    calc (p / Real.pi) * ∑ j ∈ Icc 1 B, (j : ℝ)⁻¹
        ≤ (p / Real.pi) * (1 + Real.log B) := mul_le_mul_of_nonneg_left hH hc.le
      _ < (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) := by
          apply mul_lt_mul_of_pos_left _ hc
          rw [hdecomp]
          linarith
  · have hm0' : 1 ≤ ⌊(p : ℝ) / (Real.pi * B)⌋₊ := hm0
    have hm0'' : (0 : ℝ) < ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm0
    have hR : ∑ j ∈ Icc (⌊(p : ℝ) / (Real.pi * B)⌋₊ + 1) B, (j : ℝ)⁻¹ <
        Real.log B - Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊ := by
      have h := Real.strictAnti_eulerMascheroniSeq' hmB
      unfold Real.eulerMascheroniSeq' at h
      simp only [hB0n.ne', hm0.ne', ↓reduceIte] at h
      rw [sum_Icc_succ_inv _ B hmB.le]
      linarith
    have hS : ∑ j ∈ Icc 1 B, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) <
        B * ⌊(p : ℝ) / (Real.pi * B)⌋₊ +
          (p / Real.pi) * (Real.log B - Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊) := by
      rw [hsplit]
      exact add_lt_add_right (mul_lt_mul_of_pos_left hR hc) _
    have hBT : (B : ℝ) * ((p : ℝ) / (Real.pi * B)) = p / Real.pi := by
      have hB0'' : (B : ℝ) ≠ 0 := ne_of_gt hB0
      have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
      field_simp
    have hlogBT : Real.log B - Real.log ((p : ℝ) / (Real.pi * B)) =
        Real.log (Real.pi * B ^ 2 / p) := by
      rw [← Real.log_div (ne_of_gt hB0) (ne_of_gt hT0)]
      congr 1
      have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp'
      have hB0'' : (B : ℝ) ≠ 0 := ne_of_gt hB0
      have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
      field_simp
    have hmainEq : (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) =
        (p / Real.pi) * Real.log (Real.pi * B ^ 2 / p) + (p / Real.pi) + B := by
      have hK : (p / Real.pi) * (Real.pi * B / p) = B := by
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp'
        have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
        field_simp
      linear_combination hK
    have hkey : (p / Real.pi) *
          (Real.log ((p : ℝ) / (Real.pi * B)) - Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊) ≤
        B * (((p : ℝ) / (Real.pi * B) - ⌊(p : ℝ) / (Real.pi * B)⌋₊) + 1) := by
      have hpos : (0 : ℝ) < (p : ℝ) / (Real.pi * B) / ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) :=
        div_pos hT0 hm0''
      have h := Real.log_le_sub_one_of_pos hpos
      have heq : (p : ℝ) / (Real.pi * B) / ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) - 1 =
          ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) /
            ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) := by
        have hm0''' : ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) ≠ 0 := ne_of_gt hm0''
        field_simp
      rw [heq] at h
      have hdiv : Real.log ((p : ℝ) / (Real.pi * B)) -
          Real.log ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) =
          Real.log ((p : ℝ) / (Real.pi * B) / ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) := by
        rw [Real.log_div (ne_of_gt hT0) (ne_of_gt hm0'')]
      have hsq : ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) ^ 2 ≤
          ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) := by
        have hδ0 : (0 : ℝ) ≤ (p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) := by
          linarith [hmT]
        have hδ1 : (p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) < 1 := by
          linarith [hTm]
        have hm1 : (1 : ℝ) ≤ ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm0'
        have hnn : (0 : ℝ) ≤ ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) *
            (1 - ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ))) :=
          mul_nonneg hδ0 (by linarith [hδ1])
        have hle : ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) ^ 2 ≤
            (p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) := by
          linear_combination hnn
        linarith [hle, hδ1, hm1]
      have h3 : (p : ℝ) / (Real.pi * B) *
            ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) /
            ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ) ≤
          ((p : ℝ) / (Real.pi * B) - ((⌊(p : ℝ) / (Real.pi * B)⌋₊ : ℕ) : ℝ)) + 1 := by
        rw [div_le_iff₀ hm0'']
        linear_combination hsq
      have hcT : (p / Real.pi) = (B : ℝ) * ((p : ℝ) / (Real.pi * B)) := hBT.symm
      calc (p / Real.pi) *
            (Real.log ((p : ℝ) / (Real.pi * B)) - Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊)
          = (p / Real.pi) * Real.log ((p : ℝ) / (Real.pi * B) / ⌊(p : ℝ) / (Real.pi * B)⌋₊) := by
            rw [hdiv]
        _ ≤ (p / Real.pi) * (((p : ℝ) / (Real.pi * B) - ⌊(p : ℝ) / (Real.pi * B)⌋₊) /
            ⌊(p : ℝ) / (Real.pi * B)⌋₊) := mul_le_mul_of_nonneg_left h hc.le
        _ = B * ((p : ℝ) / (Real.pi * B) * ((p : ℝ) / (Real.pi * B) - ⌊(p : ℝ) / (Real.pi * B)⌋₊) /
            ⌊(p : ℝ) / (Real.pi * B)⌋₊) := by rw [hcT]; ring
        _ ≤ B * (((p : ℝ) / (Real.pi * B) - ⌊(p : ℝ) / (Real.pi * B)⌋₊) + 1) :=
          mul_le_mul_of_nonneg_left h3 hB0.le
    have hI : (B : ℝ) * ⌊(p : ℝ) / (Real.pi * B)⌋₊ +
          (p / Real.pi) * (Real.log B - Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊) =
          (B : ℝ) * ((p : ℝ) / (Real.pi * B)) +
            (p / Real.pi) * (Real.log B - Real.log ((p : ℝ) / (Real.pi * B))) +
            ((p / Real.pi) * (Real.log ((p : ℝ) / (Real.pi * B)) -
              Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊) -
              B * ((p : ℝ) / (Real.pi * B) - ⌊(p : ℝ) / (Real.pi * B)⌋₊)) := by
      ring
    have hII : (p / Real.pi) * (Real.log ((p : ℝ) / (Real.pi * B)) -
          Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊) -
          B * ((p : ℝ) / (Real.pi * B) - ⌊(p : ℝ) / (Real.pi * B)⌋₊) ≤ B := by
      linarith [hkey]
    have hIII : (B : ℝ) * ((p : ℝ) / (Real.pi * B)) +
          (p / Real.pi) * (Real.log B - Real.log ((p : ℝ) / (Real.pi * B))) =
          (p / Real.pi) + (p / Real.pi) * Real.log (Real.pi * B ^ 2 / p) := by
      rw [hBT, hlogBT]
    rw [hmainEq]
    calc ∑ j ∈ Icc 1 B, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹)
        < B * ⌊(p : ℝ) / (Real.pi * B)⌋₊ +
            (p / Real.pi) * (Real.log B - Real.log ⌊(p : ℝ) / (Real.pi * B)⌋₊) := hS
      _ ≤ (p / Real.pi) + (p / Real.pi) * Real.log (Real.pi * B ^ 2 / p) + B := by
          rw [hI, hIII]
          linarith [hII]
      _ = (p / Real.pi) * Real.log (Real.pi * B ^ 2 / p) + (p / Real.pi) + B := by ring

end sum_min_one_div_abs_sin_lt

/-- **Bound for a truncated sum of reciprocal sines.** Let $p$ be a prime, let $a$ be an integer
not divisible by $p$, and let $B$ be an integer with $\sqrt{p/\pi} < B < p/2$. Then
$$
\sum_{h=1}^{B} \min\left\{B, \frac{1}{|\sin(\pi a h / p)|}\right\} <
\frac{p}{\pi}\left(\log\frac{\pi B^2}{p} + 1 + \frac{\pi B}{p}\right) +
\frac{pB(B+1)}{\pi(p^2 - B^2)}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.3 (`integers-2025-A48-lem-3-3`). -/
public theorem sum_min_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt (p / Real.pi) < B) (hB₂ : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, min (B : ℝ) (1 / |Real.sin (Real.pi * a * h / p)|) <
      (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hB₂' : 2 * B < p := by exact_mod_cast (show 2 * (B : ℝ) < p by linarith)
  have hB' : (B : ℝ) < p := by linarith
  have hBsq : 0 < (p : ℝ) ^ 2 - (B : ℝ) ^ 2 := by
    apply sub_pos.mpr
    gcongr
  have hpoint (j : ℕ) (hj : j ∈ Icc 1 B) :
      min (B : ℝ) (1 / Real.sin (Real.pi * j / p)) ≤
        min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) +
          (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j := by
    obtain ⟨hj₁, hjB⟩ := mem_Icc.mp hj
    have h3 := sum_one_div_abs_sin_lt.one_div_sin_lt p B j hp hB' hj₁ hjB
    have he0 : (0 : ℝ) ≤ (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j := by positivity
    exact sum_min_one_div_abs_sin_lt.min_add_le _ _ _ _ he0 h3.le
  have hcorr : (∑ j ∈ Icc 1 B, (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * (j : ℝ)) =
      p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
    rw [← mul_sum, sum_one_div_abs_sin_lt.sum_Icc_natCast]
    ring
  calc ∑ h ∈ Icc 1 B, min (B : ℝ) (1 / |Real.sin (Real.pi * a * h / p)|)
      ≤ ∑ j ∈ Icc 1 B, min (B : ℝ) (1 / Real.sin (Real.pi * j / p)) :=
        sum_one_div_abs_sin_lt.sum_le_unmultiplied p hp a ha B hB₂' (min (B : ℝ))
          fun _ _ h ↦ min_le_min le_rfl h
    _ ≤ ∑ j ∈ Icc 1 B, (min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹) +
          (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j) := sum_le_sum hpoint
    _ = (∑ j ∈ Icc 1 B, min (B : ℝ) ((p / Real.pi) * (j : ℝ)⁻¹)) +
          p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
        rw [sum_add_distrib, hcorr]
    _ < (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) +
          p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) :=
        add_lt_add_left (sum_min_one_div_abs_sin_lt.main_sum_lt p B hp hB₁) _

end MetaMathlibExt
