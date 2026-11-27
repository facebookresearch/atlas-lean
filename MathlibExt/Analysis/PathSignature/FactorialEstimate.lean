/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.RoughPath
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Convex.Slope

/-!
# Factorial decay for extensions of rough paths

An extension of finite `p`-variation inherits the factorial estimate on its first `⌊p⌋` levels
with the same control and weight, once the weight exceeds a threshold depending only on `p`.
-/

namespace MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted

open Finset Real

-- The fractional binomial coefficient, with the two lower indices as arguments.
private noncomputable def coeff (a b : ℝ) : ℝ :=
  Gamma (a + b + 1) / (Gamma (a + 1) * Gamma (b + 1))

private theorem coeff_mono_left {a A b : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) (hb : 0 ≤ b) :
    coeff a b ≤ coeff A b := by
  rcases hA.eq_or_lt with rfl | hA
  · exact le_rfl
  rcases hb.eq_or_lt with rfl | hb
  · simp [coeff, (Gamma_pos_of_pos (by linarith : 0 < a + 1)).ne',
      (Gamma_pos_of_pos (by linarith : 0 < A + 1)).ne']
  have h1 : a + 1 ∈ Set.Ioi (0 : ℝ) := show 0 < a + 1 by linarith
  have h2 : A + b + 1 ∈ Set.Ioi (0 : ℝ) := show 0 < A + b + 1 by linarith
  have hl := convexOn_log_Gamma.secant_mono_aux2 (y := a + b + 1) h1 h2
    (by linarith) (by linarith)
  have hr := convexOn_log_Gamma.secant_mono_aux3 (y := A + 1) h1 h2
    (by linarith) (by linarith)
  -- Equal-length increments of log Gamma increase with their starting point.
  have hslope := hl.trans hr
  rw [show a + b + 1 - (a + 1) = b by ring, show A + b + 1 - (A + 1) = b by ring] at hslope
  have hincr := (div_le_div_iff_of_pos_right hb).mp hslope
  simp only [Function.comp_apply] at hincr
  unfold coeff
  have ga := Gamma_pos_of_pos (by linarith : 0 < a + 1)
  have gA := Gamma_pos_of_pos (by linarith : 0 < A + 1)
  have gb := Gamma_pos_of_pos (by linarith : 0 < b + 1)
  have gab := Gamma_pos_of_pos (by linarith : 0 < a + b + 1)
  have gAb := Gamma_pos_of_pos (by linarith : 0 < A + b + 1)
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_div gab.ne' (mul_pos ga gb).ne', Real.log_div gAb.ne' (mul_pos gA gb).ne',
    Real.log_mul ga.ne' gb.ne', Real.log_mul gA.ne' gb.ne']
  linarith only [hincr]

private theorem coeff_comm (a b : ℝ) : coeff a b = coeff b a := by
  simp only [coeff, add_comm a b, mul_comm]

private theorem coeff_round {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    coeff a b ≤ ((⌈a⌉₊ + ⌈b⌉₊).choose ⌈a⌉₊ : ℝ) := by
  calc
    _ ≤ coeff ⌈a⌉₊ b := coeff_mono_left ha (Nat.le_ceil _) hb
    _ = coeff b ⌈a⌉₊ := coeff_comm _ _
    _ ≤ coeff ⌈b⌉₊ ⌈a⌉₊ := coeff_mono_left hb (Nat.le_ceil _) (by positivity)
    _ = coeff ⌈a⌉₊ ⌈b⌉₊ := coeff_comm _ _
    _ = _ := by
      rw [coeff, ← Nat.cast_add, Gamma_nat_eq_factorial, Gamma_nat_eq_factorial,
        Gamma_nat_eq_factorial, div_eq_iff (by positivity)]
      have h := (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right ⌈a⌉₊ ⌈b⌉₊)).symm
      rw [Nat.add_sub_cancel_left, mul_assoc] at h
      exact_mod_cast h

-- At most ⌈p⌉ + 1 grid points round up to a given integer.
private theorem fiber_card {p : ℝ} (hp : 0 < p) (s : Finset ℕ) (j : ℕ) :
    (s.filter fun (k : ℕ) => ⌈(k : ℝ) / p⌉₊ = j).card ≤ ⌈p⌉₊ + 1 := by
  classical
  let M := ⌊(j : ℝ) * p⌋₊
  have bounds (k : ℕ) (hk : ⌈(k : ℝ) / p⌉₊ = j) : k ≤ M ∧ M ≤ k + ⌈p⌉₊ := by
    have h := Nat.le_ceil ((k : ℝ) / p)
    have h' := Nat.ceil_lt_add_one (show 0 ≤ (k : ℝ) / p by positivity)
    rw [hk] at h h'
    refine ⟨Nat.le_floor ((div_le_iff₀ hp).mp h), ?_⟩
    have h'' : (j : ℝ) * p < k + p := by
      have := mul_lt_mul_of_pos_right h' hp
      rwa [add_mul, div_mul_cancel₀ _ hp.ne', one_mul] at this
    have hM := Nat.floor_le (show 0 ≤ (j : ℝ) * p by positivity)
    change (M : ℝ) ≤ _ at hM
    exact_mod_cast hM.trans (h''.le.trans (add_le_add_right (Nat.le_ceil p) _))
  rw [← card_range (⌈p⌉₊ + 1)]
  apply card_le_card_of_injOn (fun k => M - k)
  · intro k hk
    have := bounds k (mem_filter.mp hk).2
    simp only [mem_coe, mem_range]
    omega
  · intro k hk l hl he
    have := bounds k (mem_filter.mp hk).2
    have := bounds l (mem_filter.mp hl).2
    change M - k = M - l at he
    omega

-- On a bisection both control increments are at most half the original one. Thus
-- only the equal-argument factorial convolution is needed.
private theorem coeff_sum {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∑ k ∈ range (n + 1), coeff ((k : ℝ) / p) ((n - k : ℕ) / p) ≤
      (4 * (⌈p⌉₊ + 1 : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / p) := by
  classical
  let j (k : ℕ) := ⌈(k : ℝ) / p⌉₊
  let N := ⌊(n : ℝ) / p⌋₊ + 2
  have hN : ∀ k ∈ range (n + 1), j k + j (n - k) ≤ N := by
    intro k hk
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ (k : ℝ) / p by positivity)
    have h2 := Nat.ceil_lt_add_one (show 0 ≤ ((n - k : ℕ) : ℝ) / p by positivity)
    change (j k : ℝ) < _ at h1
    change (j (n - k) : ℝ) < _ at h2
    rw [Nat.cast_sub hkn, sub_div] at h2
    have h4 : ((j k + j (n - k) : ℕ) : ℝ) < (N : ℝ) + 1 := by
      simp only [N, Nat.cast_add, Nat.cast_ofNat]
      linarith [Nat.lt_floor_add_one ((n : ℝ) / p)]
    exact Nat.le_of_lt_succ (by exact_mod_cast h4)
  have hmap : ∀ k ∈ range (n + 1), j k ∈ range (N + 1) := by
    intro k hk
    have := hN k hk
    simp only [mem_range]
    omega
  calc
    _ ≤ ∑ k ∈ range (n + 1), (N.choose (j k) : ℝ) := by
      refine sum_le_sum fun k hk => (coeff_round (by positivity) (by positivity)).trans ?_
      exact_mod_cast Nat.choose_le_choose (j k) (hN k hk)
    _ = ∑ i ∈ range (N + 1),
        ∑ _k ∈ (range (n + 1)).filter (fun k => j k = i), (N.choose i : ℝ) :=
      (sum_fiberwise_of_maps_to' hmap (fun i => (N.choose i : ℝ))).symm
    _ ≤ ∑ i ∈ range (N + 1), (⌈p⌉₊ + 1 : ℝ) * N.choose i := by
      refine sum_le_sum fun i _ => ?_
      simp only [sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast fiber_card hp (range (n + 1)) i
    _ = (⌈p⌉₊ + 1 : ℝ) * (2 : ℝ) ^ N := by
      rw [← mul_sum]
      congr 1
      exact_mod_cast Nat.sum_range_choose N
    _ ≤ _ := by
      have h : (N : ℝ) ≤ (n : ℝ) / p + 2 := by
        simp only [N, Nat.cast_add, Nat.cast_ofNat]
        linarith [Nat.floor_le (show 0 ≤ (n : ℝ) / p by positivity)]
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h
      rw [Real.rpow_natCast, Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at this
      norm_num at this
      nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ (⌈p⌉₊ + 1 : ℝ) by positivity)]

private theorem split_norm {ι : Type*} [Fintype ι] (F G : List ι → ℝ) (n k : ℕ) (hk : k ≤ n) :
    ∑ f : Fin n → ι, |F ((List.ofFn f).take k) * G ((List.ofFn f).drop k)| =
      levelNorm F k * levelNorm G (n - k) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, ← (Fin.appendEquiv k l).sum_comp, Fintype.sum_prod_type]
  rw [levelNorm, levelNorm, sum_mul]
  simp [Fin.appendEquiv, mul_sum, abs_mul]

private theorem tensor_bound {ι : Type*} [Fintype ι] (F G : List ι → ℝ) (n : ℕ) :
    levelNorm (tensorMul F G) n ≤
      ∑ k ∈ range (n + 1), levelNorm F k * levelNorm G (n - k) := by
  simp only [levelNorm, tensorMul, List.length_ofFn]
  calc
    _ ≤ ∑ f : Fin n → ι, ∑ k ∈ range (n + 1),
        |F ((List.ofFn f).take k) * G ((List.ofFn f).drop k)| :=
      sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [sum_comm]
      exact sum_congr rfl fun k hk => split_norm F G n k (by simpa [Nat.lt_succ_iff] using hk)

private theorem control_half {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) :
    ∃ u ∈ J, s ≤ u ∧ u ≤ t ∧ ω s u ≤ ω s t / 2 ∧ ω u t ≤ ω s t / 2 := by
  have hmem : Set.Icc s t ⊆ J := hJ.out hs ht
  have hc : ContinuousOn (ω s) (Set.Icc s t) :=
    hω.1.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨hs, hmem hu, hu.1⟩)
  have hnn := hω.2.2.1 s hs t ht hst
  obtain ⟨u, hu, he⟩ := intermediate_value_Icc hst hc
    (show ω s t / 2 ∈ Set.Icc (ω s s) (ω s t) by rw [hω.2.1 s hs]; constructor <;> linarith)
  exact ⟨u, hmem hu, hu.1, hu.2, he.le, by
    linarith [hω.2.2.2 s hs u (hmem hu) t ht hu.1 hu.2]⟩

private noncomputable def weight (p β : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  z ^ ((n : ℝ) / p) / (β * Gamma ((n : ℝ) / p + 1))

private theorem weight_nonneg {p β z : ℝ} (hp : 0 < p) (hβ : 0 < β) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ weight p β n z :=
  div_nonneg (Real.rpow_nonneg hz _) (mul_pos hβ (Gamma_pos_of_pos (by positivity))).le

private theorem weight_mono {p β x y : ℝ} (hp : 0 < p) (hβ : 0 < β) (n : ℕ)
    (hx : 0 ≤ x) (hxy : x ≤ y) : weight p β n x ≤ weight p β n y := by
  unfold weight
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hx hxy (by positivity))
    (mul_pos hβ (Gamma_pos_of_pos (by positivity))).le

private theorem weight_half {p β z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    weight p β n (z / 2) = weight p β n z / (2 : ℝ) ^ ((n : ℝ) / p) := by
  rw [weight, weight, Real.div_rpow hz (by norm_num)]
  ring

private theorem weight_mul {p β z : ℝ} (hp : 0 < p) (hβ : 0 < β) (hz : 0 ≤ z)
    {n k : ℕ} (hk : k ≤ n) :
    weight p β k z * weight p β (n - k) z =
      weight p β n z / β * coeff ((k : ℝ) / p) ((n - k : ℕ) / p) := by
  have he : (k : ℝ) / p + ((n - k : ℕ) : ℝ) / p = (n : ℝ) / p := by
    rw [Nat.cast_sub hk, sub_div]; ring
  unfold weight coeff
  rw [he, div_mul_div_comm, ← Real.rpow_add_of_nonneg hz (by positivity) (by positivity), he]
  field_simp [(Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) / p + 1)).ne']

private theorem middle_bound {p β z : ℝ} (hp : 0 < p) (hβ : 0 < β) (hz : 0 ≤ z) (n : ℕ) :
    ∑ k ∈ range (n + 1), weight p β k (z / 2) * weight p β (n - k) (z / 2) ≤
      (4 * (⌈p⌉₊ + 1 : ℝ) / β) * weight p β n z := by
  calc
    _ = weight p β n (z / 2) / β *
        ∑ k ∈ range (n + 1), coeff ((k : ℝ) / p) ((n - k : ℕ) / p) := by
      rw [mul_sum]
      exact sum_congr rfl fun k hk => weight_mul hp hβ (by positivity)
        (by simpa [Nat.lt_succ_iff] using hk)
    _ ≤ weight p β n (z / 2) / β * _ :=
      mul_le_mul_of_nonneg_left (coeff_sum hp n)
        (div_nonneg (weight_nonneg hp hβ (by positivity) _) hβ.le)
    _ = _ := by
      rw [weight_half hz]
      field_simp

private theorem sum_ends (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range (m + 1 + 1), f k =
      (∑ k ∈ range m, f (k + 1)) + f 0 + f (m + 1) := by
  rw [sum_range_succ, sum_range_succ']

private theorem convolution_bound (A B W : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hA : A 0 = 1) (hB : B 0 = 1) (hBnn : ∀ j, 0 ≤ B j) (hW : ∀ j, 0 ≤ W j)
    (ha : ∀ j, 0 < j → j < n → A j ≤ W j) (hb : ∀ j, 0 < j → j < n → B j ≤ W j) :
    ∑ k ∈ range (n + 1), A k * B (n - k) ≤
      A n + B n + ∑ k ∈ range (n + 1), W k * W (n - k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [sum_ends, sum_ends]
  simp only [Nat.sub_zero, Nat.sub_self, hA, hB, one_mul, mul_one]
  have h : ∑ k ∈ range m, A (k + 1) * B (m + 1 - (k + 1)) ≤
      ∑ k ∈ range m, W (k + 1) * W (m + 1 - (k + 1)) := by
    refine sum_le_sum fun k hk => ?_
    have := mem_range.mp hk
    exact mul_le_mul (ha _ (by omega) (by omega)) (hb _ (by omega) (by omega)) (hBnn _) (hW _)
  linarith [mul_nonneg (hW 0) (hW (m + 1)), mul_nonneg (hW (m + 1)) (hW 0)]

private def LevelBound {ι : Type*} [Fintype ι] (p β : ℝ) (n : ℕ)
    (Y : ℝ → ℝ → List ι → ℝ) (ω : ℝ → ℝ → ℝ) (J : Set ℝ) (K : ℝ) : Prop :=
  ∀ s ∈ J, ∀ t ∈ J, s ≤ t → levelNorm (Y s t) n ≤ K * weight p β n (ω s t)

-- A single bisection contracts any previously known bound at level n.
private theorem improve {ι : Type*} [Fintype ι] {p β : ℝ} (hp : 0 < p) (hβ : 0 < β)
    {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ} (hω : IsControl ω J)
    {n : ℕ} (hn : 0 < n) {Y : ℝ → ℝ → List ι → ℝ} (hY : IsMultiplicativeFunctional n Y J)
    (hlo : ∀ j, 0 < j → j < n → LevelBound p β j Y ω J 1)
    {K : ℝ} (hK : 0 ≤ K) (hprev : LevelBound p β n Y ω J K) :
    LevelBound p β n Y ω J
      (2 / (2 : ℝ) ^ ((n : ℝ) / p) * K + 4 * (⌈p⌉₊ + 1 : ℝ) / β) := by
  intro s hs t ht hst
  obtain ⟨u, hu, hsu, hut, hleft, hright⟩ := control_half hJ hω hs ht hst
  let A := levelNorm (Y s u)
  let B := levelNorm (Y u t)
  let W := fun k => weight p β k (ω s t / 2)
  have hnn := hω.2.2.1
  have hz := hnn s hs t ht hst
  have ha (k : ℕ) (hk : 0 < k) (hkn : k < n) : A k ≤ W k := calc
    _ ≤ weight p β k (ω s u) := by simpa using hlo k hk hkn s hs u hu hsu
    _ ≤ _ := weight_mono hp hβ _ (hnn _ hs _ hu hsu) hleft
  have hb (k : ℕ) (hk : 0 < k) (hkn : k < n) : B k ≤ W k := calc
    _ ≤ weight p β k (ω u t) := by simpa using hlo k hk hkn u hu t ht hut
    _ ≤ _ := weight_mono hp hβ _ (hnn _ hu _ ht hut) hright
  have hAn : A n ≤ K * W n := (hprev _ hs _ hu hsu).trans <|
    mul_le_mul_of_nonneg_left (weight_mono hp hβ _ (hnn _ hs _ hu hsu) hleft) hK
  have hBn : B n ≤ K * W n := (hprev _ hu _ ht hut).trans <|
    mul_le_mul_of_nonneg_left (weight_mono hp hβ _ (hnn _ hu _ ht hut) hright) hK
  calc
    _ = levelNorm (tensorMul (Y s u) (Y u t)) n := by
      apply sum_congr rfl
      intro f _
      rw [hY.2 s hs u hu t ht hsu hut (List.ofFn f) (by simp)]
    _ ≤ ∑ k ∈ range (n + 1), A k * B (n - k) := tensor_bound _ _ _
    _ ≤ A n + B n + ∑ k ∈ range (n + 1), W k * W (n - k) :=
      convolution_bound A B W hn (by simp [A, levelNorm, hY.1 _ hs _ hu hsu])
        (by simp [B, levelNorm, hY.1 _ hu _ ht hut])
        (fun _ => sum_nonneg fun _ _ => abs_nonneg _)
        (fun _ => weight_nonneg hp hβ (by positivity) _) ha hb
    _ ≤ (K * W n + K * W n) + (4 * (⌈p⌉₊ + 1 : ℝ) / β) * weight p β n (ω s t) :=
      add_le_add (add_le_add hAn hBn) (middle_bound hp hβ hz n)
    _ = _ := by dsimp only [W]; rw [weight_half hz]; ring

private theorem remove_excess {ι : Type*} [Fintype ι] {p β : ℝ} (hp : 0 < p) (hβ : 0 < β)
    {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ} (hω : IsControl ω J)
    {n : ℕ} (hn : 0 < n) {Y : ℝ → ℝ → List ι → ℝ} (hY : IsMultiplicativeFunctional n Y J)
    (hlo : ∀ j, 0 < j → j < n → LevelBound p β j Y ω J 1)
    (hq : 2 / (2 : ℝ) ^ ((n : ℝ) / p) + 4 * (⌈p⌉₊ + 1 : ℝ) / β ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) (hprev : LevelBound p β n Y ω J K) :
    LevelBound p β n Y ω J 1 := by
  let q := 2 / (2 : ℝ) ^ ((n : ℝ) / p)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    linarith [show 0 < 4 * (⌈p⌉₊ + 1 : ℝ) / β by positivity]
  have hiter (l : ℕ) : LevelBound p β n Y ω J (1 + q ^ l * K) := by
    induction l with
    | zero =>
      intro s hs t ht hst
      have hw := weight_nonneg hp hβ (hω.2.2.1 s hs t ht hst) n
      exact (hprev _ hs _ ht hst).trans <| mul_le_mul_of_nonneg_right (by simp) hw
    | succ l ih =>
      have h := improve hp hβ hJ hω hn hY hlo (by positivity) ih
      intro s hs t ht hst
      refine (h _ hs _ ht hst).trans (mul_le_mul_of_nonneg_right ?_
        (weight_nonneg hp hβ (hω.2.2.1 s hs t ht hst) _))
      change q * _ + _ ≤ _
      rw [pow_succ]
      change q + _ ≤ 1 at hq
      linarith
  intro s hs t ht hst
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const K
  have hlim' := (Filter.Tendsto.const_add 1 hlim).mul_const (weight p β n (ω s t))
  exact ge_of_tendsto' (by simpa only [zero_mul, add_zero] using hlim')
    (fun l => hiter l s hs t ht hst)

private theorem control_add_mul {J : Set ℝ} {ω η : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) (hη : IsControl η J) {ε : ℝ} (hε : 0 < ε) :
    IsControl (fun s t => ω s t + ε * η s t) J := by
  refine ⟨hω.1.add (continuousOn_const.mul hη.1), ?_, ?_, ?_⟩
  · intro t ht
    simp [hω.2.1 t ht, hη.2.1 t ht]
  · intro s hs t ht hst
    exact add_nonneg (hω.2.2.1 _ hs _ ht hst) (mul_nonneg hε.le (hη.2.2.1 _ hs _ ht hst))
  · intro r hr s hs t ht hrs hst
    have h := mul_le_mul_of_nonneg_left (hη.2.2.2 _ hr _ hs _ ht hrs hst) hε.le
    linarith [hω.2.2.2 _ hr _ hs _ ht hrs hst]

-- Finite variation supplies a preliminary bound with a possibly different control η.
-- Adding εη makes that bound available on every subinterval during the bisection.
private theorem extend_level {ι : Type*} [Fintype ι] {p β : ℝ} (hp : 0 < p) (hβ : 0 < β)
    {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ} (hω : IsControl ω J)
    {n : ℕ} (hn : 0 < n) {Y : ℝ → ℝ → List ι → ℝ} (hY : IsMultiplicativeFunctional n Y J)
    (hfin : HasFinitePVariation p n Y J)
    (hlo : ∀ j, 0 < j → j < n → LevelBound p β j Y ω J 1)
    (hq : 2 / (2 : ℝ) ^ ((n : ℝ) / p) + 4 * (⌈p⌉₊ + 1 : ℝ) / β ≤ 1) :
    LevelBound p β n Y ω J 1 := by
  obtain ⟨η, hη, b, hb, hctl⟩ := hfin
  have hpert (ε : ℝ) (hε : 0 < ε) :
      LevelBound p β n Y (fun s t => ω s t + ε * η s t) J 1 := by
    let K := β / (b * ε ^ ((n : ℝ) / p))
    apply remove_excess hp hβ hJ (control_add_mul hω hη hε) hn hY _ hq
      (show 0 ≤ K by dsimp [K]; positivity)
    · intro s hs t ht hst
      have hx := hη.2.2.1 _ hs _ ht hst
      calc
        _ ≤ weight p b n (η s t) := hctl n hn le_rfl s hs t ht hst
        _ = K * weight p β n (ε * η s t) := by
          dsimp only [K, weight]
          rw [Real.mul_rpow hε.le hx]
          field_simp [(Real.rpow_pos_of_pos hε ((n : ℝ) / p)).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (weight_mono hp hβ _ (mul_nonneg hε.le hx) (le_add_of_nonneg_left
            (hω.2.2.1 _ hs _ ht hst))) (by dsimp [K]; positivity)
    · intro j hj hjn s hs t ht hst
      refine (hlo j hj hjn _ hs _ ht hst).trans ?_
      simp only [one_mul]
      exact weight_mono hp hβ _ (hω.2.2.1 _ hs _ ht hst)
        (le_add_of_nonneg_right (mul_nonneg hε.le (hη.2.2.1 _ hs _ ht hst)))
  intro s hs t ht hst
  simp only [one_mul]
  have hc : Continuous fun ε : ℝ => weight p β n (ω s t + ε * η s t) :=
    ((Real.continuous_rpow_const (by positivity : 0 ≤ (n : ℝ) / p)).comp
      (continuous_const.add (continuous_id.mul continuous_const))).div_const _
  have htend := (hc.continuousWithinAt (x := 0) (s := Set.Ioi 0)).tendsto
  apply ge_of_tendsto (by simpa only [zero_mul, add_zero] using htend)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa only [one_mul] using hpert ε hε s hs t ht hst

/-- **Lyons's extension theorem: the factorial estimate.** For `p ≥ 1` there is `β₀ > 0` such that,
whenever `β ≥ β₀`, `ω` is a control on an interval `J` and the levels `1, …, ⌊p⌋` of a
multiplicative functional `X` satisfy `‖Xⁱ_{s,t}‖ ≤ ω(s, t)^{i/p} / (β (i/p)!)`, its extension
`Y` (multiplicative of every degree, of finite `p`-variation, agreeing with `X` up to level
`⌊p⌋`) satisfies the same inequality in every degree (T. Lyons, *Differential equations driven by
rough signals*, Rev. Mat. Iberoam. 14 (1998), Theorem 2.2.1, inequalities (2.20) and (2.21):
"providing β is large enough"; Remark 2.2.1(1) gives an explicit sufficient `β` depending only
on `p`, through the Riemann zeta function, for any admissible family of tensor norms). Here `β₀`
depends only on `p`: it is chosen before the alphabet. -/
public theorem isControlledBy_extension {p : ℝ} (hp : 1 ≤ p) :
    ∃ β₀ > 0, ∀ (ι : Type) [Fintype ι] {J : Set ℝ}, J.OrdConnected → ∀ (ω : ℝ → ℝ → ℝ),
      IsControl ω J →
      ∀ β ≥ β₀, ∀ X Y : ℝ → ℝ → List ι → ℝ,
        IsMultiplicativeFunctional ⌊p⌋₊ X J → IsControlledBy p β ⌊p⌋₊ X ω J →
        (∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Y s t w = X s t w) →
        (∀ m, IsMultiplicativeFunctional m Y J ∧ HasFinitePVariation p m Y J) →
        ∀ m, IsControlledBy p β m Y ω J := by
  have hp0 : 0 < p := by linarith
  let q := 2 / (2 : ℝ) ^ (((⌊p⌋₊ : ℝ) + 1) / p)
  have hq : q < 1 := by
    apply (div_lt_one (by positivity)).mpr
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        ((one_lt_div hp0).mpr (Nat.lt_floor_add_one p))
  let C : ℝ := 4 * (⌈p⌉₊ + 1 : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C / (1 - q), div_pos hC (sub_pos.mpr hq), ?_⟩
  intro ι _ J hJ ω hω β hlarge X Y _ hX hagree hY
  have hβ : 0 < β := (div_pos hC (sub_pos.mpr hq)).trans_le hlarge
  have hroom : C / β ≤ 1 - q := by
    apply (div_le_iff₀ hβ).mpr
    linarith [(div_le_iff₀ (sub_pos.mpr hq)).mp hlarge]
  have hall (n : ℕ) : 0 < n → LevelBound p β n Y ω J 1 := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      by_cases hlow : n ≤ ⌊p⌋₊
      · intro s hs t ht hst
        have he : levelNorm (Y s t) n = levelNorm (X s t) n := by
          apply sum_congr rfl
          intro f _
          rw [hagree s hs t ht hst (List.ofFn f) (by simpa using hlow)]
        rw [he, one_mul]
        exact hX _ hn hlow _ hs _ ht hst
      · refine extend_level hp0 hβ hJ hω hn (hY n).1 (hY n).2
          (fun j hj hjn => ih j hjn hj) ?_
        have he : (⌊p⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.lt_of_not_ge hlow
        have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (div_le_div_of_nonneg_right he hp0.le)
        have hfrac : 2 / (2 : ℝ) ^ ((n : ℝ) / p) ≤ q :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
        change _ + C / β ≤ 1
        linarith
  intro m i hi _ s hs t ht hst
  simpa only [one_mul, weight] using hall i hi _ hs _ ht hst

end MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted
