/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

/-!
# Sparse recovery in ℓ₁

Under the restricted isometry property, `sum_abs_sub_le_of_hasRIP` bounds the ℓ₁ error of
basis pursuit by the ℓ₁ mass outside any set of at most `s` coordinates, and
`sqrt_sum_sq_sub_le_of_hasRIP_of_noisy` bounds the ℓ₂ error of basis pursuit from noisy
measurements by the same mass divided by `√s` plus a multiple of the noise level.
-/

@[expose] public section

open Finset Matrix MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

namespace MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted

/-- The vector equal to `h` on `W` and zero elsewhere (Candès's `h_W`). -/
private def restr {ι : Type*} [DecidableEq ι] (h : ι → ℝ) (W : Finset ι) : ι → ℝ :=
  fun j => if j ∈ W then h j else 0

private lemma restr_of_notMem {ι : Type*} [DecidableEq ι] {h : ι → ℝ} {W : Finset ι}
    {j : ι} (hj : j ∉ W) :
    restr h W j = 0 := by
  simp [restr, hj]

private lemma sum_restr_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (W : Finset ι) :
    ∑ j, restr h W j ^ 2 = ∑ j ∈ W, h j ^ 2 := by
  simp [restr, ite_pow, sum_ite_mem]

/-- Among the indices of `R`, a set `T` of `min s #R` indices carrying the largest entries of
`|h|`. -/
private lemma exists_top {ι : Type*} [DecidableEq ι] (h : ι → ℝ) (R : Finset ι) (s : ℕ) :
    ∃ T ⊆ R, #T = min s #R ∧ ∀ j ∈ T, ∀ k ∈ R \ T, |h k| ≤ |h j| := by
  obtain ⟨T, hT, hmax⟩ := (R.powersetCard (min s #R)).exists_max_image
    (fun T => ∑ j ∈ T, |h j|) (powersetCard_nonempty.mpr (min_le_right _ _))
  rw [mem_powersetCard] at hT
  refine ⟨T, hT.1, hT.2, fun j hj k hk => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rw [mem_sdiff] at hk
  have hkT : k ∉ T.erase j := fun h => hk.2 (mem_of_mem_erase h)
  have hT' : insert k (T.erase j) ∈ R.powersetCard (min s #R) := by
    rw [mem_powersetCard]
    refine ⟨insert_subset hk.1 ((erase_subset _ _).trans hT.1), ?_⟩
    rw [card_insert_of_notMem hkT, card_erase_of_mem hj, hT.2]
    have := card_pos.mpr ⟨j, hj⟩
    omega
  have hle := hmax _ hT'
  have hsum : ∑ i ∈ insert k (T.erase j), |h i| = ∑ i ∈ T, |h i| - |h j| + |h k| := by
    rw [sum_insert hkT, ← add_sum_erase T _ hj]
    ring
  linarith

/-- The `ℓ₂` norm of `h_W` is at most `M / √s` when `#W ≤ s` and `s |h j| ≤ s t ≤ M` on `W`. -/
private lemma sqrt_sum_restr_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → ℝ}
    {W : Finset ι} {s : ℕ}
    (hs : 1 ≤ s) (hW : #W ≤ s) {t M : ℝ} (ht : 0 ≤ t) (hbound : ∀ j ∈ W, |h j| ≤ t)
    (hM : s * t ≤ M) :
    √(∑ j, restr h W j ^ 2) ≤ M / √s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  rw [sum_restr_sq]
  have h1 : ∑ j ∈ W, h j ^ 2 ≤ s * t ^ 2 := by
    calc ∑ j ∈ W, h j ^ 2 ≤ ∑ _j ∈ W, t ^ 2 := sum_le_sum fun j hj => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbound j hj) 2
      _ = #W * t ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ s * t ^ 2 := by gcongr
  calc √(∑ j ∈ W, h j ^ 2) ≤ √(s * t ^ 2) := Real.sqrt_le_sqrt h1
    _ = √s * t := by rw [Real.sqrt_mul hs0.le, Real.sqrt_sq ht]
    _ ≤ M / √s := by
      rw [le_div_iff₀ hsq, mul_comm, ← mul_assoc, Real.mul_self_sqrt hs0.le]
      exact hM

/-- The blockwise estimate of Candès (2008), (10) with Lemma 2.1: for `u` supported on `U` with
`#U ≤ s` and `W` disjoint from `U`, if `|h| ≤ t` on `W` and `s t ≤ M`, then
`|⟪Φ u, Φ h_W⟫| ≤ δ ‖u‖₂ (M + ‖h_W‖₁) / √s`. Proved by peeling off the `s` largest entries of
`h` on `W` (Candès's blocks `T₂, T₃, …`). -/
private lemma abs_dotProduct_restr_le {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hs : 1 ≤ s)
    (hΦ : HasRIP Φ (s + s) δ) (hδ : 0 ≤ δ) (h u : ι → ℝ) {U : Finset ι} (hU : #U ≤ s)
    (hu : ∀ j ∉ U, u j = 0) :
    ∀ (n : ℕ) (W : Finset ι), #W ≤ n → Disjoint U W → ∀ t M : ℝ, 0 ≤ t →
      (∀ j ∈ W, |h j| ≤ t) → s * t ≤ M →
      |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ restr h W)| ≤
        δ * √(∑ j, u j ^ 2) * ((M + ∑ j ∈ W, |h j|) / √s) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  have hδu : 0 ≤ δ * √(∑ j, u j ^ 2) := mul_nonneg hδ (Real.sqrt_nonneg _)
  have hW1 : ∀ W : Finset ι, 0 ≤ ∑ j ∈ W, |h j| := fun W => sum_nonneg fun j _ => abs_nonneg _
  have base : ∀ W : Finset ι, #W ≤ s → Disjoint U W → ∀ t M : ℝ, 0 ≤ t →
      (∀ j ∈ W, |h j| ≤ t) → s * t ≤ M →
      |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ restr h W)| ≤ δ * √(∑ j, u j ^ 2) * (M / √s) := by
    intro W hW hUW t M ht hbound hM
    refine (abs_dotProduct_mulVec_le hΦ hU hW hUW hu fun j hj => restr_of_notMem hj).trans ?_
    exact mul_le_mul_of_nonneg_left (sqrt_sum_restr_sq_le hs hW ht hbound hM) hδu
  intro n
  induction n with
  | zero =>
    intro W hW hUW t M ht hbound hM
    refine (base W (hW.trans (Nat.zero_le _)) hUW t M ht hbound hM).trans ?_
    gcongr
    exact le_add_of_nonneg_right (hW1 W)
  | succ n ih =>
    intro W hW hUW t M ht hbound hM
    by_cases hWs : #W ≤ s
    · refine (base W hWs hUW t M ht hbound hM).trans ?_
      gcongr
      exact le_add_of_nonneg_right (hW1 W)
    rw [not_le] at hWs
    obtain ⟨T, hTW, hTcard, htop⟩ := exists_top h W s
    rw [min_eq_left hWs.le] at hTcard
    have hsplit : restr h W = restr h T + restr h (W \ T) := by
      funext j
      by_cases hjT : j ∈ T
      · simp [restr, hjT, hTW hjT]
      · by_cases hjW : j ∈ W <;> simp [restr, hjT, hjW]
    have hT := base T hTcard.le (disjoint_of_subset_right hTW hUW) t M ht
      (fun j hj => hbound j (hTW hj)) hM
    have hrest := ih (W \ T) (by rw [card_sdiff_of_subset hTW]; omega)
      (disjoint_of_subset_right sdiff_subset hUW) ((∑ j ∈ T, |h j|) / s) (∑ j ∈ T, |h j|)
      (div_nonneg (hW1 T) hs0.le)
      (fun k hk => by
        rw [le_div_iff₀ hs0]
        calc |h k| * s = ∑ _j ∈ T, |h k| := by rw [sum_const, hTcard, nsmul_eq_mul, mul_comm]
          _ ≤ ∑ j ∈ T, |h j| := sum_le_sum fun j hj => htop j hj k hk)
      (by rw [mul_div_cancel₀ _ hs0.ne'])
    have hsum : ∑ j ∈ T, |h j| + ∑ j ∈ W \ T, |h j| = ∑ j ∈ W, |h j| := by
      rw [add_comm, sum_sdiff hTW]
    rw [hsplit, mulVec_add, dotProduct_add]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ δ * √(∑ j, u j ^ 2) * (M / √s) +
          δ * √(∑ j, u j ^ 2) * ((∑ j ∈ T, |h j| + ∑ j ∈ W \ T, |h j|) / √s) :=
          add_le_add hT hrest
      _ = δ * √(∑ j, u j ^ 2) * ((M + ∑ j ∈ W, |h j|) / √s) := by
          rw [hsum]; ring

/-- The cone constraint obtained by comparing the ℓ₁ norms on `S` and its complement. -/
private lemma sum_abs_sub_compl_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x xhat : ι → ℝ} (hle : ∑ j, |xhat j| ≤ ∑ j, |x j|) (S : Finset ι) :
    ∑ j ∈ Sᶜ, |xhat j - x j| ≤ ∑ j ∈ S, |xhat j - x j| + 2 * ∑ j ∈ Sᶜ, |x j| := by
  have hhead := sum_le_sum (s := S) fun j _ =>
    (abs_sub_abs_le_abs_sub (x j) (xhat j)).trans_eq (abs_sub_comm _ _)
  have htail := sum_le_sum (s := Sᶜ) fun j _ => abs_sub (xhat j) (x j)
  rw [sum_sub_distrib] at hhead
  rw [sum_add_distrib] at htail
  rw [← sum_add_sum_compl S (fun j => |xhat j|), ← sum_add_sum_compl S (fun j => |x j|)] at hle
  linarith

set_option maxHeartbeats 800000 in
-- The block-peeling proof below is long; the default limit is exceeded near its end.
/-- The `ℓ₂` estimate at the heart of Candès (2008), Theorems 1.2 and 1.3: with `h` split
into its `s` largest entries off `T₀`, the next block and the tail, the restricted isometry
property and Lemma 2.1 bound the first two blocks by the measurement residual `B` and the
`ℓ₁` mass off `T₀`, and every tail entry is at most the average of the first block, so the
tail contributes at most the same `ℓ₁` mass divided by `√s`. -/
private lemma sqrt_sum_sq_le_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hs : 1 ≤ s) (hΦ : HasRIP Φ (2 * s) δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : ι → ℝ} {B : ℝ} (hB : √(∑ i, (Φ *ᵥ h) i ^ 2) ≤ B)
    (hB0 : 0 ≤ B) {T₀ : Finset ι} (hT₀ : #T₀ ≤ s) :
    √(∑ j, h j ^ 2) ≤ √(1 + δ) / (1 - δ) * B +
      (1 + √2 * δ / (1 - δ)) * ((∑ j ∈ T₀ᶜ, |h j|) / √s) ∧
      ∑ j ∈ T₀, |h j| ≤ √s * (√(1 + δ) / (1 - δ) * B) +
        (√2 * δ / (1 - δ)) * ∑ j ∈ T₀ᶜ, |h j| := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  have hΦ' : HasRIP Φ (s + s) δ := by rwa [← two_mul]
  obtain ⟨T₁, hT₁R, hT₁card, htop⟩ := exists_top h T₀ᶜ s
  set W := T₀ᶜ \ T₁ with hWdef
  set M := ∑ j ∈ T₁, |h j| with hMdef
  have hT₁s : #T₁ ≤ s := hT₁card.trans_le (min_le_left _ _)
  have hdisj01 : Disjoint T₀ T₁ := disjoint_of_subset_right hT₁R disjoint_compl_right
  have hdisj0W : Disjoint T₀ W := disjoint_of_subset_right sdiff_subset disjoint_compl_right
  have hdisj1W : Disjoint T₁ W := disjoint_sdiff
  have hM0 : 0 ≤ M := sum_nonneg fun j _ => abs_nonneg _
  have hbound : ∀ k ∈ W, |h k| ≤ M / s := by
    intro k hk
    have hcard : #T₁ = s := by
      by_contra hne
      have hlt : #T₀ᶜ < s := by
        rcases le_total s #T₀ᶜ with hle | hle
        · rw [min_eq_left hle] at hT₁card; exact absurd hT₁card hne
        · rw [min_eq_right hle] at hT₁card; omega
      have : T₁ = T₀ᶜ := eq_of_subset_of_card_le hT₁R (by
        rw [hT₁card]; exact (min_eq_right hlt.le).ge)
      rw [hWdef, this, sdiff_self] at hk
      exact absurd hk (notMem_empty k)
    rw [le_div_iff₀ hs0]
    calc |h k| * s = ∑ _j ∈ T₁, |h k| := by rw [sum_const, hcard, nsmul_eq_mul, mul_comm]
      _ ≤ M := sum_le_sum fun j hj => htop j hj k hk
  set K := (M + ∑ j ∈ W, |h j|) / √s with hK
  have hKL : M + ∑ j ∈ W, |h j| = ∑ j ∈ T₀ᶜ, |h j| := by
    rw [add_comm, hMdef, hWdef, sum_sdiff hT₁R]
  have hK0 : 0 ≤ K := div_nonneg (by rw [hKL]; exact sum_nonneg fun j _ => abs_nonneg _) hsq.le
  have hb0 := abs_dotProduct_restr_le hs hΦ' hδ0 h (restr h T₀) hT₀
    (fun j hj => restr_of_notMem hj) _ W le_rfl hdisj0W (M / s) M
    (div_nonneg hM0 hs0.le) hbound (by rw [mul_div_cancel₀ _ hs0.ne'])
  have hb1 := abs_dotProduct_restr_le hs hΦ' hδ0 h (restr h T₁) hT₁s
    (fun j hj => restr_of_notMem hj) _ W le_rfl hdisj1W (M / s) M
    (div_nonneg hM0 hs0.le) hbound (by rw [mul_div_cancel₀ _ hs0.ne'])
  rw [← hK] at hb0 hb1
  have hdecomp : h = restr h T₀ + restr h T₁ + restr h W := by
    funext j
    by_cases h0 : j ∈ T₀
    · have h1 : j ∉ T₁ := disjoint_left.mp hdisj01 h0
      have h2 : j ∉ W := disjoint_left.mp hdisj0W h0
      simp [restr, h0, h1, h2]
    · by_cases h1 : j ∈ T₁
      · have h2 : j ∉ W := disjoint_left.mp hdisj1W h1
        simp [restr, h0, h1, h2]
      · have h2 : j ∈ W := by rw [hWdef, mem_sdiff, mem_compl]; exact ⟨h0, h1⟩
        simp [restr, h0, h1, h2]
  set u := restr h T₀ + restr h T₁ with hu
  have husp : hammingNorm u ≤ 2 * s := by
    refine (hammingNorm_le_card (T := T₀ ∪ T₁) fun j hj => ?_).trans
      ((card_union_le _ _).trans (by omega))
    rw [mem_union, not_or] at hj
    simp [hu, restr, hj.1, hj.2]
  set A := ∑ j ∈ T₀, h j ^ 2 with hA
  set Bsq := ∑ j ∈ T₁, h j ^ 2 with hBsq
  have hA0 : 0 ≤ A := sum_nonneg fun j _ => sq_nonneg _
  have hB0' : 0 ≤ Bsq := sum_nonneg fun j _ => sq_nonneg _
  have hunorm : ∑ j, u j ^ 2 = A + Bsq := by
    have : u = restr h (T₀ ∪ T₁) := by
      funext j
      by_cases h0 : j ∈ T₀
      · have h1 : j ∉ T₁ := disjoint_left.mp hdisj01 h0
        simp [hu, restr, h0, h1]
      · by_cases h1 : j ∈ T₁ <;> simp [hu, restr, h0, h1]
    rw [this, sum_restr_sq, sum_union hdisj01]
  obtain ⟨hlow, hup⟩ := hΦ u husp
  rw [hunorm] at hlow hup
  have hΦh : Φ *ᵥ h = Φ *ᵥ u + Φ *ᵥ restr h W := by rw [← mulVec_add, ← hdecomp]
  have hΦu_eq : Φ *ᵥ u = Φ *ᵥ restr h T₀ + Φ *ᵥ restr h T₁ := by
    rw [hu, mulVec_add]
  have hΦu2 : ∑ i, (Φ *ᵥ u) i ^ 2 =
      (Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h) - (Φ *ᵥ restr h T₀) ⬝ᵥ (Φ *ᵥ restr h W) -
        (Φ *ᵥ restr h T₁) ⬝ᵥ (Φ *ᵥ restr h W) := by
    have hpt : ∀ i, (Φ *ᵥ u) i ^ 2 = (Φ *ᵥ u) i * (Φ *ᵥ h) i -
        (Φ *ᵥ restr h T₀) i * (Φ *ᵥ restr h W) i -
          (Φ *ᵥ restr h T₁) i * (Φ *ᵥ restr h W) i := by
      intro i
      have hi1 : (Φ *ᵥ u) i = (Φ *ᵥ restr h T₀) i + (Φ *ᵥ restr h T₁) i := by
        rw [hΦu_eq]; rfl
      have hi2 : (Φ *ᵥ h) i = (Φ *ᵥ u) i + (Φ *ᵥ restr h W) i := by
        rw [hΦh]; rfl
      rw [hi2, hi1]; ring
    rw [show (∑ i, (Φ *ᵥ u) i ^ 2) =
      ∑ i, ((Φ *ᵥ u) i * (Φ *ᵥ h) i - (Φ *ᵥ restr h T₀) i * (Φ *ᵥ restr h W) i -
        (Φ *ᵥ restr h T₁) i * (Φ *ᵥ restr h W) i) from
      sum_congr rfl fun i _ => hpt i]
    simp only [dotProduct, sum_sub_distrib]
  rw [sum_restr_sq] at hb0 hb1
  set a := √A with ha
  set b := √Bsq with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0' : 0 ≤ b := Real.sqrt_nonneg _
  set N := √(A + Bsq) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN2 : N ^ 2 = A + Bsq := Real.sq_sqrt (by positivity)
  have hPu : √(∑ i, (Φ *ᵥ u) i ^ 2) ≤ √(1 + δ) * N := by
    calc √(∑ i, (Φ *ᵥ u) i ^ 2) ≤ √((1 + δ) * (A + Bsq)) := Real.sqrt_le_sqrt hup
      _ = √(1 + δ) * N := by rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 + δ)]
  have hCS : |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h)| ≤
      √(∑ i, (Φ *ᵥ u) i ^ 2) * √(∑ i, (Φ *ᵥ h) i ^ 2) := by
    have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun i => (Φ *ᵥ u) i) (fun i => (Φ *ᵥ h) i)
    have hdot : (Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h) =
        ∑ i, (Φ *ᵥ u) i * (Φ *ᵥ h) i := rfl
    calc |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h)| = √(((Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h)) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ = √((∑ i, (Φ *ᵥ u) i * (Φ *ᵥ h) i) ^ 2) := by rw [hdot]
      _ ≤ √((∑ i, (Φ *ᵥ u) i ^ 2) * ∑ i, (Φ *ᵥ h) i ^ 2) := Real.sqrt_le_sqrt hcs2
      _ = √(∑ i, (Φ *ᵥ u) i ^ 2) * √(∑ i, (Φ *ᵥ h) i ^ 2) := by
          rw [Real.sqrt_mul (sum_nonneg fun i _ => sq_nonneg _)]
  have hdot : (Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h) ≤ √(1 + δ) * N * B := by
    calc (Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h) ≤ |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ h)| := le_abs_self _
      _ ≤ √(∑ i, (Φ *ᵥ u) i ^ 2) * √(∑ i, (Φ *ᵥ h) i ^ 2) := hCS
      _ ≤ √(∑ i, (Φ *ᵥ u) i ^ 2) * B :=
          mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
      _ ≤ (√(1 + δ) * N) * B := mul_le_mul_of_nonneg_right hPu hB0
      _ = √(1 + δ) * N * B := by ring
  have hmain : (1 - δ) * (A + Bsq) ≤ √(1 + δ) * N * B + δ * (a + b) * K := by
    have h0 := neg_abs_le ((Φ *ᵥ restr h T₀) ⬝ᵥ (Φ *ᵥ restr h W))
    have h1 := neg_abs_le ((Φ *ᵥ restr h T₁) ⬝ᵥ (Φ *ᵥ restr h W))
    linarith [hlow, hΦu2, hdot, hb0, hb1, h0, h1]
  have hab : a + b ≤ √2 * N := by
    have h2 : (a + b) ^ 2 ≤ 2 * (A + Bsq) := by
      have hsqA := Real.sq_sqrt hA0
      have hsqB := Real.sq_sqrt hB0'
      nlinarith [sq_nonneg (a - b)]
    calc a + b = √((a + b) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(2 * (A + Bsq)) := Real.sqrt_le_sqrt h2
      _ = √2 * N := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpos : 0 < 1 - δ := by linarith
  have hmul : (1 - δ) * N ≤ √(1 + δ) * B + √2 * δ * K := by
    rcases hN0.eq_or_lt with hN00 | hN00
    · rw [← hN00]
      simp only [mul_zero]
      positivity
    · have h2 : (1 - δ) * N * N ≤ (√(1 + δ) * B + √2 * δ * K) * N := by
        calc (1 - δ) * N * N = (1 - δ) * (A + Bsq) := by rw [← hN2]; ring
          _ ≤ √(1 + δ) * N * B + δ * (a + b) * K := hmain
          _ ≤ √(1 + δ) * N * B + δ * (√2 * N) * K := by
              gcongr
          _ = (√(1 + δ) * B + √2 * δ * K) * N := by ring
      exact le_of_mul_le_mul_right h2 hN00
  have hNle : N ≤ √(1 + δ) / (1 - δ) * B + (√2 * δ / (1 - δ)) * K := by
    have h' : N ≤ (√(1 + δ) * B + √2 * δ * K) / (1 - δ) :=
      (le_div_iff₀ hpos).2 (by linarith [hmul])
    rw [show √(1 + δ) / (1 - δ) * B + (√2 * δ / (1 - δ)) * K =
      (√(1 + δ) * B + √2 * δ * K) / (1 - δ) by
      field_simp]
    exact h'
  have hWsq : ∑ j ∈ W, h j ^ 2 ≤ K ^ 2 := by
    have hper : ∑ j ∈ W, h j ^ 2 ≤ (M / s) * ∑ j ∈ W, |h j| := by
      calc ∑ j ∈ W, h j ^ 2 ≤ ∑ j ∈ W, (M / s) * |h j| := sum_le_sum fun j hj => by
            calc h j ^ 2 = |h j| ^ 2 := (sq_abs _).symm
              _ = |h j| * |h j| := by ring
              _ ≤ (M / s) * |h j| :=
                  mul_le_mul_of_nonneg_right (hbound j hj) (abs_nonneg _)
        _ = (M / s) * ∑ j ∈ W, |h j| := by rw [mul_sum]
    have hS0 : 0 ≤ ∑ j ∈ W, |h j| := sum_nonneg fun j _ => abs_nonneg _
    have hMle : M ≤ ∑ j ∈ T₀ᶜ, |h j| := by
      rw [← hKL]; exact le_add_of_nonneg_right hS0
    calc ∑ j ∈ W, h j ^ 2 ≤ (M / s) * ∑ j ∈ W, |h j| := hper
      _ ≤ K ^ 2 := by
        rw [hK, div_pow, Real.sq_sqrt hs0.le]
        have h1 : (M / s) * ∑ j ∈ W, |h j| = (M * ∑ j ∈ W, |h j|) / s := by
          rw [div_mul_eq_mul_div]
        rw [h1]
        gcongr
        nlinarith [sq_nonneg M, sq_nonneg (∑ j ∈ W, |h j|), mul_nonneg hM0 hS0]
  have hpt : ∀ j, h j ^ 2 = u j ^ 2 + restr h W j ^ 2 := by
    intro j
    by_cases hjW : j ∈ W
    · have h0 : j ∉ T₀ := fun h0 => (disjoint_left.mp hdisj0W h0) hjW
      have h1 : j ∉ T₁ := fun h1 => (disjoint_left.mp hdisj1W h1) hjW
      have hu0 : u j = 0 := by simp [hu, restr, h0, h1]
      simp [hu0, restr, hjW]
    · have hr0 : restr h W j = 0 := restr_of_notMem hjW
      have hu : u j = h j := by
        have hcong := congrFun hdecomp j
        simp only [Pi.add_apply, hu, hr0, add_zero] at hcong
        exact hcong.symm
      simp [hr0, hu]
  have htot : ∑ j, h j ^ 2 = (A + Bsq) + ∑ j ∈ W, h j ^ 2 := by
    calc ∑ j, h j ^ 2 = ∑ j, (u j ^ 2 + restr h W j ^ 2) := sum_congr rfl fun j _ => hpt j
      _ = ∑ j, u j ^ 2 + ∑ j, restr h W j ^ 2 := sum_add_distrib
      _ = (A + Bsq) + ∑ j ∈ W, h j ^ 2 := by rw [hunorm, sum_restr_sq]
  have hsqrt : √(∑ j, h j ^ 2) ≤ N + K := by
    rw [htot, ← Real.sqrt_sq (add_nonneg hN0 hK0)]
    apply Real.sqrt_le_sqrt
    calc (A + Bsq) + ∑ j ∈ W, h j ^ 2 ≤ (A + Bsq) + K ^ 2 := add_le_add le_rfl hWsq
      _ = N ^ 2 + K ^ 2 := by rw [← hN2]
      _ ≤ (N + K) ^ 2 := by
          rw [add_pow_two]
          linarith [mul_nonneg hN0 hK0]
  have hKE : K = (∑ j ∈ T₀ᶜ, |h j|) / √s := by rw [hK, hKL]
  have hL2 : √(∑ j, h j ^ 2) ≤ √(1 + δ) / (1 - δ) * B +
      (1 + √2 * δ / (1 - δ)) * ((∑ j ∈ T₀ᶜ, |h j|) / √s) := by
    calc √(∑ j, h j ^ 2) ≤ N + K := hsqrt
      _ ≤ (√(1 + δ) / (1 - δ) * B + (√2 * δ / (1 - δ)) * K) + K := by linarith [hNle]
      _ = √(1 + δ) / (1 - δ) * B +
          (1 + √2 * δ / (1 - δ)) * ((∑ j ∈ T₀ᶜ, |h j|) / √s) := by rw [hKE]; ring
  have hcs : ∑ j ∈ T₀, |h j| ≤ √s * a := by
    have h1 : (∑ j ∈ T₀, |h j|) ^ 2 ≤ s * A := by
      calc (∑ j ∈ T₀, |h j|) ^ 2 ≤ #T₀ * ∑ j ∈ T₀, |h j| ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ = #T₀ * A := by
            congr 1
            rw [hA]
            exact sum_congr rfl fun j _ => sq_abs _
        _ ≤ s * A := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT₀) hA0
    calc ∑ j ∈ T₀, |h j| ≤ √(s * A) := (le_abs_self _).trans (Real.abs_le_sqrt h1)
      _ = √s * a := by rw [Real.sqrt_mul hs0.le, ← ha]
  have haN : a ≤ N := Real.sqrt_le_sqrt (by linarith)
  have hTbound : ∑ j ∈ T₀, |h j| ≤ √s * (√(1 + δ) / (1 - δ) * B) +
      (√2 * δ / (1 - δ)) * ∑ j ∈ T₀ᶜ, |h j| := by
    have hsqne : √(s : ℝ) ≠ 0 := hsq.ne'
    calc ∑ j ∈ T₀, |h j| ≤ √s * a := hcs
      _ ≤ √s * N := by gcongr
      _ ≤ √s * (√(1 + δ) / (1 - δ) * B + (√2 * δ / (1 - δ)) * K) := by gcongr
      _ = √s * (√(1 + δ) / (1 - δ) * B) +
          (√2 * δ / (1 - δ)) * ∑ j ∈ T₀ᶜ, |h j| := by
          rw [hKE, mul_add]
          congr 1
          field_simp
  exact ⟨hL2, hTbound⟩

/-- **Noiseless recovery, `ℓ₁` error** (E. J. Candès, *The restricted isometry property and its
implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592,
Theorem 1.2, eq. (4)): let `s ≥ 1` and let `Φ` have the restricted isometry property of order
`2 s` with a constant `δ < √2 - 1`. Let `xhat` be a solution of `min ‖x̃‖₁` subject to
`Φ x̃ = Φ x`. Then `‖xhat - x‖₁ ≤ C₀ ‖x - x_s‖₁` with `C₀ = 2 (1 + ρ) / (1 - ρ)` and
`ρ = √2 δ / (1 - δ)`; here `‖x - x_s‖₁` is replaced by `∑_{j ∉ S} |x j|` for an arbitrary set
`S` of at most `s` indices, an equivalent formulation since `x_s` is the best `s`-term
approximation of `x`. -/
theorem sum_abs_sub_le_of_hasRIP {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} (hs : 1 ≤ s) {δ : ℝ} (hΦ : HasRIP Φ (2 * s) δ)
    (hδ : δ < √2 - 1) {x xhat : ι → ℝ} (hfeas : Φ *ᵥ xhat = Φ *ᵥ x)
    (hmin : ∀ w : ι → ℝ, Φ *ᵥ w = Φ *ᵥ x → ∑ j, |xhat j| ≤ ∑ j, |w j|)
    {S : Finset ι} (hS : #S ≤ s) :
    ∑ j, |xhat j - x j| ≤
      2 * (1 + √2 * δ / (1 - δ)) / (1 - √2 * δ / (1 - δ)) * ∑ j ∈ Sᶜ, |x j| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.univ_eq_empty, Finset.eq_empty_of_isEmpty Sᶜ]
  have hδ1 : δ < 1 := by
    have : √(2 : ℝ) < 2 := by norm_num [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    linarith
  set ρ := √2 * δ / (1 - δ)
  have hρ0 : 0 ≤ ρ :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hΦ.nonneg (by omega))) (sub_nonneg.mpr hδ1.le)
  have hρ : ρ < 1 := by
    rw [div_lt_one (sub_pos.mpr hδ1)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      mul_pos (sub_pos.mpr hδ) (show 0 < √(2 : ℝ) + 1 by positivity)]
  have hker : Φ *ᵥ (xhat - x) = 0 := by rw [mulVec_sub, hfeas, sub_self]
  have hnull := sum_abs_le_of_mulVec_eq_zero hs hΦ hδ1 hker hS
  change ∑ j ∈ S, |xhat j - x j| ≤ ρ * ∑ j ∈ Sᶜ, |xhat j - x j| at hnull
  have hcone := sum_abs_sub_compl_le (hmin x rfl) S
  have htail : ∑ j ∈ Sᶜ, |xhat j - x j| ≤ (2 * ∑ j ∈ Sᶜ, |x j|) / (1 - ρ) := by
    apply (le_div_iff₀ (sub_pos.mpr hρ)).2
    linarith only [hcone, hnull]
  calc
    ∑ j, |xhat j - x j| = ∑ j ∈ S, |xhat j - x j| + ∑ j ∈ Sᶜ, |xhat j - x j| :=
      (sum_add_sum_compl S _).symm
    _ ≤ (1 + ρ) * ∑ j ∈ Sᶜ, |xhat j - x j| := by linarith only [hnull]
    _ ≤ (1 + ρ) * ((2 * ∑ j ∈ Sᶜ, |x j|) / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-- **Noisy recovery** (E. J. Candès, *The restricted isometry property and its implications for
compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Theorem 1.3, eq. (8)):
let `s ≥ 1` and let `Φ` have the restricted isometry property of order `2 s` with a constant
`δ < √2 - 1`. Observe `y = Φ x + z` with `‖z‖₂ ≤ ε`, and let `xhat` be a solution of
`min ‖x̃‖₁` subject to `‖y - Φ x̃‖₂ ≤ ε` (problem (7)). Then
`‖xhat - x‖₂ ≤ C₀ s^{-1/2} ‖x - x_s‖₁ + C₁ ε` with `ρ = √2 δ / (1 - δ)`,
`α = 2 √(1 + δ) / (1 - δ)`, `C₀ = 2 (1 + ρ) / (1 - ρ)` and `C₁ = 2 α / (1 - ρ)`; here
`‖x - x_s‖₁` is replaced by `∑_{j ∉ S} |x j|` for an arbitrary set `S` of at most `s` indices,
an equivalent formulation since `x_s` is the best `s`-term approximation of `x`. -/
theorem sqrt_sum_sq_sub_le_of_hasRIP_of_noisy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} (hs : 1 ≤ s) {δ : ℝ} (hΦ : HasRIP Φ (2 * s) δ)
    (hδ : δ < √2 - 1) {x xhat : ι → ℝ} {y z : Fin m → ℝ} (hy : y = Φ *ᵥ x + z) {ε : ℝ}
    (hz : √(∑ i, z i ^ 2) ≤ ε) (hfeas : √(∑ i, (y - Φ *ᵥ xhat) i ^ 2) ≤ ε)
    (hmin : ∀ w : ι → ℝ, √(∑ i, (y - Φ *ᵥ w) i ^ 2) ≤ ε → ∑ j, |xhat j| ≤ ∑ j, |w j|)
    {S : Finset ι} (hS : #S ≤ s) :
    √(∑ j, (xhat j - x j) ^ 2) ≤
      2 * (1 + √2 * δ / (1 - δ)) / (1 - √2 * δ / (1 - δ)) / √s * ∑ j ∈ Sᶜ, |x j| +
        2 * (2 * √(1 + δ) / (1 - δ)) / (1 - √2 * δ / (1 - δ)) * ε := by
  have hδ1 : δ < 1 := by
    have : √(2 : ℝ) < 2 := by norm_num [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hρ : √2 * δ / (1 - δ) < 1 := by
    rw [div_lt_one (sub_pos.mpr hδ1)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      mul_pos (sub_pos.mpr hδ) (show 0 < √(2 : ℝ) + 1 by positivity)]
  have hε : 0 ≤ ε := (Real.sqrt_nonneg _).trans hz
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hL : √(∑ j, (xhat j - x j) ^ 2) = 0 := by simp [Finset.univ_eq_empty]
    have hR0 : ∑ j ∈ Sᶜ, |x j| = 0 := by simp [Finset.eq_empty_of_isEmpty Sᶜ]
    have hcoeff : 0 ≤ 2 * (2 * √(1 + δ) / (1 - δ)) / (1 - √2 * δ / (1 - δ)) := by
      apply div_nonneg _ (sub_nonneg.mpr hρ.le)
      positivity
    rw [hL, hR0, mul_zero, zero_add]
    exact mul_nonneg hcoeff hε
  have hδ0 : 0 ≤ δ := hΦ.nonneg (by omega)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  set ρ := √2 * δ / (1 - δ) with hρdef
  set α := 2 * √(1 + δ) / (1 - δ) with hαdef
  have hρ0 : 0 ≤ ρ := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hδ0) (sub_nonneg.mpr hδ1.le)
  have hD : 0 < 1 - ρ := sub_pos.mpr hρ
  have hxfeas : √(∑ i, (y - Φ *ᵥ x) i ^ 2) ≤ ε := by
    have hsub : y - Φ *ᵥ x = z := by rw [hy, add_sub_cancel_left]
    rw [hsub]; exact hz
  have hle : ∑ j, |xhat j| ≤ ∑ j, |x j| := hmin x hxfeas
  have hcone := sum_abs_sub_compl_le hle S
  -- The triangle inequality for `√(∑ · ^ 2)`, from Cauchy–Schwarz.
  have htri : ∀ a b : Fin m → ℝ, √(∑ i, (a i + b i) ^ 2) ≤
      √(∑ i, a i ^ 2) + √(∑ i, b i ^ 2) := by
    intro a b
    have hcs : ∑ i, a i * b i ≤ √(∑ i, a i ^ 2) * √(∑ i, b i ^ 2) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
      calc ∑ i, a i * b i ≤ |∑ i, a i * b i| := le_abs_self _
        _ = √((∑ i, a i * b i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √((∑ i, a i ^ 2) * ∑ i, b i ^ 2) := Real.sqrt_le_sqrt h
        _ = √(∑ i, a i ^ 2) * √(∑ i, b i ^ 2) := by
            rw [Real.sqrt_mul (sum_nonneg fun i _ => sq_nonneg _)]
    have hsum : ∑ i, (a i + b i) ^ 2 =
        ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
      calc ∑ i, (a i + b i) ^ 2 = ∑ i, (a i ^ 2 + 2 * (a i * b i) + b i ^ 2) :=
            sum_congr rfl fun i _ => by ring
        _ = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
            simp only [sum_add_distrib, mul_sum]
    have hsq2 : ∑ i, (a i + b i) ^ 2 ≤
        (√(∑ i, a i ^ 2) + √(∑ i, b i ^ 2)) ^ 2 := by
      rw [hsum, add_pow_two, Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _),
        Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)]
      linarith [hcs]
    calc √(∑ i, (a i + b i) ^ 2) ≤
          √((√(∑ i, a i ^ 2) + √(∑ i, b i ^ 2)) ^ 2) := Real.sqrt_le_sqrt hsq2
      _ = √(∑ i, a i ^ 2) + √(∑ i, b i ^ 2) :=
          Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hres : √(∑ i, (Φ *ᵥ (xhat - x)) i ^ 2) ≤ 2 * ε := by
    have hΦh : Φ *ᵥ (xhat - x) = (Φ *ᵥ xhat - y) + z := by
      funext i
      rw [mulVec_sub]
      simp [hy]
      ring
    rw [hΦh]
    calc √(∑ i, ((Φ *ᵥ xhat - y) + z) i ^ 2) ≤
          √(∑ i, (Φ *ᵥ xhat - y) i ^ 2) + √(∑ i, z i ^ 2) :=
          htri _ _
      _ = √(∑ i, (y - Φ *ᵥ xhat) i ^ 2) + √(∑ i, z i ^ 2) := by
          rw [show (∑ i, (Φ *ᵥ xhat - y) i ^ 2) = ∑ i, (y - Φ *ᵥ xhat) i ^ 2 from
            sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring]
      _ ≤ ε + ε := add_le_add hfeas hz
      _ = 2 * ε := by ring
  obtain ⟨hL2, hTbound⟩ := sqrt_sum_sq_le_aux hs hΦ hδ0 hδ1 hres (by linarith) (T₀ := S) hS
  simp only [Pi.sub_apply] at hL2 hTbound
  have hαeq : √(1 + δ) / (1 - δ) * (2 * ε) = α * ε := by rw [hαdef]; ring
  have hT : ∑ j ∈ S, |xhat j - x j| ≤ √s * (α * ε) + ρ * ∑ j ∈ Sᶜ, |xhat j - x j| := by
    calc ∑ j ∈ S, |xhat j - x j| ≤ √s * (√(1 + δ) / (1 - δ) * (2 * ε)) +
          ρ * ∑ j ∈ Sᶜ, |xhat j - x j| := hTbound
      _ = √s * (α * ε) + ρ * ∑ j ∈ Sᶜ, |xhat j - x j| := by rw [hαeq]
  have hE : (1 - ρ) * ∑ j ∈ Sᶜ, |xhat j - x j| ≤
      2 * ∑ j ∈ Sᶜ, |x j| + √s * (α * ε) := by linarith [hcone, hT]
  have hmul : (1 - ρ) * √(∑ j, (xhat j - x j) ^ 2) ≤
      2 * (1 + ρ) / √s * ∑ j ∈ Sᶜ, |x j| + 2 * α * ε := by
    have h1 : (1 - ρ) * √(∑ j, (xhat j - x j) ^ 2) ≤
        (1 - ρ) * (√(1 + δ) / (1 - δ) * (2 * ε) +
          (1 + ρ) * ((∑ j ∈ Sᶜ, |xhat j - x j|) / √s)) :=
      mul_le_mul_of_nonneg_left hL2 hD.le
    have h2 : (1 - ρ) * ((1 + ρ) * ((∑ j ∈ Sᶜ, |xhat j - x j|) / √s)) ≤
        (1 + ρ) / √s * (2 * ∑ j ∈ Sᶜ, |x j| + √s * (α * ε)) := by
      have hrw : (1 - ρ) * ((1 + ρ) * ((∑ j ∈ Sᶜ, |xhat j - x j|) / √s)) =
          (1 + ρ) / √s * ((1 - ρ) * ∑ j ∈ Sᶜ, |xhat j - x j|) := by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hE (by positivity)
    have h3 : (1 - ρ) * (√(1 + δ) / (1 - δ) * (2 * ε)) +
        (1 + ρ) / √s * (2 * ∑ j ∈ Sᶜ, |x j| + √s * (α * ε)) =
        2 * (1 + ρ) / √s * ∑ j ∈ Sᶜ, |x j| + 2 * α * ε := by
      rw [hαeq]
      have hsqne : √(s : ℝ) ≠ 0 := hsq.ne'
      field_simp
      ring
    linarith [h1, h2, h3]
  have hEq : 2 * (1 + ρ) / (1 - ρ) / √s * ∑ j ∈ Sᶜ, |x j| +
        2 * α / (1 - ρ) * ε =
      (2 * (1 + ρ) / √s * ∑ j ∈ Sᶜ, |x j| + 2 * α * ε) / (1 - ρ) := by
    field_simp
  rw [show 2 * (2 * √(1 + δ) / (1 - δ)) / (1 - √2 * δ / (1 - δ)) * ε = 2 * α / (1 - ρ) * ε by
    rw [hαdef, hρdef]]
  rw [show 2 * (1 + √2 * δ / (1 - δ)) / (1 - √2 * δ / (1 - δ)) / √s * ∑ j ∈ Sᶜ, |x j| =
    2 * (1 + ρ) / (1 - ρ) / √s * ∑ j ∈ Sᶜ, |x j| by rw [hρdef]]
  rw [hEq]
  exact (le_div_iff₀ hD).2 (by linarith [hmul])

end MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted
