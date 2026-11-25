/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FreeProbability.Freeness
public import MathlibExt.Combinatorics.NoncrossingPartition.Pairing
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.Chain
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The free central limit theorem

For free centered variables of unit variance with uniformly bounded moments of each order,
`free_central_limit` proves convergence in moments of their normalized sums to the semicircle law.

Multiplication by a summand prepends a letter to a reduced word when the first index differs.
When the indices agree, centering the product gives a new letter plus a scalar times the tail.
After normalization, the leading terms change the word length by one in either direction.
At the empty word they count walks returning to zero, which gives the Catalan moments.
The remaining terms contribute an error of order at most `1 / √N` for each fixed moment.
-/

open Filter Topology Finset
open scoped ComplexOrder
open MathlibExt.Probability.FreeProbability NoncrossingPartition

namespace MathlibExt.Probability.FreeProbabilityWanted.free_central_limit

variable {A : Type*} [Ring A] [Algebra ℂ A]

-- Iterated centering within the algebra of one variable.
private noncomputable def letter (φ : A →ₗ[ℂ] ℂ) (x : A) : ℕ → A
  | 0 => x
  | k + 1 => x * letter φ x k - φ (x * letter φ x k) • 1

private noncomputable def weight (φ : A →ₗ[ℂ] ℂ) (x : A) (k : ℕ) : ℂ := φ (x * letter φ x k)

private lemma letter_mem (φ : A →ₗ[ℂ] ℂ) (x : A) (k : ℕ) :
    letter φ x k ∈ Algebra.adjoin ℂ ({x} : Set A) := by
  have hx : x ∈ Algebra.adjoin ℂ ({x} : Set A) := Algebra.subset_adjoin (by simp)
  induction k with
  | zero => exact hx
  | succ k ih => exact sub_mem (mul_mem hx ih) (Subalgebra.smul_mem _ (one_mem _) _)

private lemma letter_centered (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) {x : A} (hx : φ x = 0)
    (k : ℕ) : φ (letter φ x k) = 0 := by
  cases k with
  | zero => exact hx
  | succ k => simp [letter, hφ]

private lemma weight_bounded (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖weight φ (a i) k‖ ≤ C := by
  suffices ∀ k m : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ m * letter φ (a i) k)‖ ≤ C by
    obtain ⟨C, hC⟩ := this k 1
    exact ⟨C, (norm_nonneg _).trans (hC 0), fun i => by simpa [weight] using hC i⟩
  intro n
  induction n with
  | zero => intro m; simpa [letter, ← pow_succ] using hbdd (m + 1)
  | succ n ih =>
    intro m
    obtain ⟨B, hB⟩ := ih (m + 1)
    obtain ⟨D, hD⟩ := ih 1
    obtain ⟨E, hE⟩ := hbdd m
    refine ⟨B + D * E, fun i => ?_⟩
    simp only [letter, mul_sub, ← mul_assoc, ← pow_succ, mul_smul_comm, mul_one,
      map_sub, map_smul, smul_eq_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hB i) (by
      rw [norm_mul]
      exact mul_le_mul (by simpa using hD i) (hE i) (norm_nonneg _)
        ((norm_nonneg _).trans (hD i))))

private abbrev Word (N : ℕ) := List (Fin N × ℕ)

private def Reduced {N : ℕ} (w : Word N) := w.IsChain (fun u v => u.1 ≠ v.1)

private noncomputable def evalWord (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) {N : ℕ} (w : Word N) : A :=
  (w.map (fun v => letter φ (a v.1) v.2)).prod

private noncomputable def mass (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) {N : ℕ} (w : Word N) : ℂ :=
  (w.map (fun v => weight φ (a v.1) v.2)).prod

private lemma evalWord_cons_centered (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : ℕ → A)
    (hf : AreFree φ hφ a) (hm : ∀ i, φ (a i) = 0) {N : ℕ} (u : Fin N × ℕ)
    (w : Word N) (hr : Reduced (u :: w)) : φ (evalWord φ a (u :: w)) = 0 := by
  let l := u :: w
  let idx (i : Fin (w.length + 1)) := (l.get i).1
  let val (i : Fin (w.length + 1)) := letter φ (a (idx i)) (l.get i).2
  have h := hf w.length (fun i => (idx i : ℕ)) val (fun i hij => ?_)
    (fun i => letter_mem φ _ _) (fun i => letter_centered φ hφ (hm _) _)
  · have he : List.ofFn val = l.map (fun v => letter φ (a v.1) v.2) :=
      List.ofFn_getElem_eq_map l (fun v => letter φ (a v.1) v.2)
    rwa [he] at h
  · apply (List.isChain_iff_getElem.mp hr i (by simp))
    exact Fin.ext hij

-- For a word of length h we scale its mixed moment by (√N)^h.
private noncomputable def root (N : ℕ) : ℂ := (Real.sqrt N : ℝ)

private noncomputable def normalized (a : ℕ → A) (N : ℕ) : A :=
  (root N)⁻¹ • ∑ i : Fin N, a i

private noncomputable def moment (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (p : ℕ) {N : ℕ}
    (w : Word N) : ℂ := root N ^ w.length * φ (normalized a N ^ p * evalWord φ a w)

private lemma root_sq (N : ℕ) : root N ^ 2 = N := by
  unfold root
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

private lemma root_ne {N : ℕ} (hN : 0 < N) : root N ≠ 0 := by
  simp [root, hN.ne']

private lemma moment_step (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (p : ℕ) {N : ℕ} (hN : 0 < N)
    (w : Word N) : moment φ a (p + 1) w =
      (N : ℂ)⁻¹ * ∑ i : Fin N, moment φ a p ((i, 0) :: w) := by
  have hr := root_ne hN
  rw [← root_sq]
  simp only [moment, pow_succ, normalized, smul_mul_assoc, mul_smul_comm,
    map_smul, smul_eq_mul, List.length_cons, evalWord,
    List.map_cons, List.prod_cons, letter, ← mul_assoc, ← Finset.mul_sum]
  field_simp
  simp [Finset.mul_sum, Finset.sum_mul, map_sum]

-- At a repeated index the product splits into its centered and scalar parts.
private lemma moment_hit (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (p : ℕ) {N : ℕ} (hN : 0 < N)
    (i : Fin N) (k : ℕ) (w : Word N) :
    (N : ℂ)⁻¹ * moment φ a p ((i, 0) :: (i, k) :: w) =
      (root N)⁻¹ * moment φ a p ((i, k + 1) :: w) +
        weight φ (a i) k * moment φ a p w := by
  have hr := root_ne hN
  rw [← root_sq]
  simp only [moment, evalWord, List.map_cons, List.prod_cons, List.length_cons, letter,
    sub_mul, smul_mul_assoc, one_mul, mul_sub, mul_smul_comm, map_sub, map_smul, smul_eq_mul,
    mul_assoc, weight, pow_succ]
  field_simp
  ring

-- The limiting recursion counts walks on the nonnegative integers ending at zero.
private def walks : ℕ → ℕ → ℂ
  | 0, h => if h = 0 then 1 else 0
  | p + 1, 0 => walks p 1
  | p + 1, h + 1 => walks p (h + 2) + walks p h

-- Scaling the remainder by √N makes all the error estimates uniform in N.
private noncomputable def error (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (p : ℕ) {N : ℕ}
    (w : Word N) : ℂ :=
  root N * (moment φ a p w - walks p w.length * mass φ a w)

private lemma mass_cons (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) {N : ℕ} (i : Fin N) (k : ℕ)
    (w : Word N) :
    mass φ a ((i, k) :: w) = weight φ (a i) k * mass φ a w := by simp [mass]

private lemma mass_push (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (hv : ∀ i, φ (a i ^ 2) = 1)
    {N : ℕ} (i : Fin N) (w : Word N) : mass φ a ((i, 0) :: w) = mass φ a w := by
  simp [mass_cons, weight, letter, ← sq, hv]

private lemma error_step (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (hv : ∀ i, φ (a i ^ 2) = 1)
    (p : ℕ) {N : ℕ} (hN : 0 < N) (w : Word N) : error φ a (p + 1) w =
      (N : ℂ)⁻¹ * ∑ j : Fin N, error φ a p ((j, 0) :: w) +
        root N * ((walks p (w.length + 1) - walks (p + 1) w.length) * mass φ a w) := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [error, moment_step φ a p hN, mass_push φ a hv, List.length_cons, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma error_nil (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (hv : ∀ i, φ (a i ^ 2) = 1)
    (p : ℕ) {N : ℕ} (hN : 0 < N) : error φ a (p + 1) ([] : Word N) =
      (N : ℂ)⁻¹ * ∑ j : Fin N, error φ a p [(j, 0)] := by
  simp [error_step φ a hv p hN, walks]

-- At a nonempty word, fresh indices contribute the average over all but its first index.
-- The repeated index can raise the first degree or remove the first letter. The two
-- last terms account for raising the degree and for the missing summand in the average.
private lemma error_cons (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A) (hv : ∀ i, φ (a i ^ 2) = 1)
    (p : ℕ) {N : ℕ} (hN : 0 < N) (i : Fin N) (k : ℕ) (w : Word N) :
    error φ a (p + 1) ((i, k) :: w) =
      (N : ℂ)⁻¹ * ∑ j ∈ univ.erase i, error φ a p ((j, 0) :: (i, k) :: w) +
      (root N)⁻¹ * error φ a p ((i, k + 1) :: w) +
      weight φ (a i) k * error φ a p w +
      walks p (w.length + 1) * mass φ a ((i, k + 1) :: w) -
      (root N)⁻¹ * (walks p (w.length + 2) * mass φ a ((i, k) :: w)) := by
  rw [error_step φ a hv p hN, ← sum_erase_add _ _ (mem_univ i), mul_add]
  have hr := root_ne hN
  have hit := moment_hit φ a p hN i k w
  simp only [error, List.length_cons, walks, mass_push φ a hv, mass_cons]
  rw [← root_sq] at hit ⊢
  field_simp at hit ⊢
  linear_combination (norm := ring_nf) root N * hit
  simp [sub_eq_add_neg, add_comm]

private lemma mass_bounded (φ : A →ₗ[ℂ] ℂ) (a : ℕ → A)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C) (d : List ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} (w : Word N), w.map Prod.snd = d → ‖mass φ a w‖ ≤ C := by
  induction d with
  | nil =>
    refine ⟨1, by norm_num, ?_⟩
    intro N w hw
    simp_all [mass]
  | cons k d ih =>
    obtain ⟨B, hB, hb⟩ := weight_bounded φ a hbdd k
    obtain ⟨C, _, hc⟩ := ih
    refine ⟨B * C, by positivity, ?_⟩
    intro N w hw
    obtain _ | ⟨⟨i, k'⟩, w⟩ := w
    · simp at hw
    simp only [List.map_cons, List.cons.injEq] at hw
    obtain ⟨rfl, hw⟩ := hw
    rw [mass_cons, norm_mul]
    exact mul_le_mul (hb _) (hc _ hw) (norm_nonneg _) hB

private lemma norm_average_le {N : ℕ} (hN : 0 < N) (s : Finset (Fin N)) (f : Fin N → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ j ∈ s, ‖f j‖ ≤ C) :
    ‖(N : ℂ)⁻¹ * ∑ j ∈ s, f j‖ ≤ C := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc
    ‖∑ j ∈ s, f j‖ ≤ ∑ j ∈ s, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, C := sum_le_sum hf
    _ ≤ N * C := by
      simp only [sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast (s.card_le_univ.trans_eq (Fintype.card_fin N))

private lemma norm_inv_root_le {N : ℕ} (hN : 0 < N) : ‖(root N)⁻¹‖ ≤ 1 := by
  simp only [root, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N from hN)))

-- A word's degree list fixes the finitely many one-variable moment bounds needed here.
private lemma error_bounded (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : ℕ → A)
    (hf : AreFree φ hφ a) (hm : ∀ i, φ (a i) = 0) (hv : ∀ i, φ (a i ^ 2) = 1)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C) (p : ℕ) (d : List ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 0 < N → ∀ w : Word N,
      w.map Prod.snd = d → Reduced w → ‖error φ a p w‖ ≤ C := by
  induction p generalizing d with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro N hN w hw hr
    cases w with
    | nil => simp [error, moment, walks, evalWord, mass, hφ]
    | cons v w => simp [error, moment, walks, evalWord_cons_centered φ hφ a hf hm _ _ hr]
  | succ p ih =>
    cases d with
    | nil =>
      obtain ⟨B, hB, hb⟩ := ih [0]
      refine ⟨B, hB, ?_⟩
      intro N hN w hw hr
      obtain rfl : w = [] := by simpa using hw
      rw [error_nil φ a hv p hN]
      exact norm_average_le hN _ _ hB (fun j _ => hb hN _ rfl (.singleton _))
    | cons k d =>
      obtain ⟨B, hB, hb⟩ := ih (0 :: k :: d)
      obtain ⟨D, _, hd⟩ := ih ((k + 1) :: d)
      obtain ⟨E, _, he⟩ := ih d
      obtain ⟨F, hF, hf'⟩ := weight_bounded φ a hbdd k
      obtain ⟨G, _, hg⟩ := mass_bounded φ a hbdd ((k + 1) :: d)
      obtain ⟨H, _, hh⟩ := mass_bounded φ a hbdd (k :: d)
      refine ⟨B + D + F * E + ‖walks p (d.length + 1)‖ * G +
        ‖walks p (d.length + 2)‖ * H, by positivity, ?_⟩
      intro N hN w hw hr
      obtain _ | ⟨⟨i, k'⟩, w⟩ := w
      · simp at hw
      simp only [List.map_cons, List.cons.injEq] at hw
      obtain ⟨rfl, hw⟩ := hw
      have hlen : w.length = d.length := by simpa using congrArg List.length hw
      have hinc : Reduced ((i, k' + 1) :: w) := by
        apply List.isChain_cons.mpr
        exact ⟨(List.isChain_cons.mp hr).1, (List.isChain_cons.mp hr).2⟩
      rw [error_cons φ a hv p hN i k' w]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · refine norm_average_le hN _ _ hB (fun j hj => hb hN _ (by simp [hw]) ?_)
              exact List.isChain_cons_cons.mpr ⟨ne_of_mem_erase hj, hr⟩
            · rw [norm_mul]
              exact (mul_le_mul_of_nonneg_right (norm_inv_root_le hN) (norm_nonneg _)).trans
                (by simpa using hd hN _ (by simp [hw]) hinc)
          · rw [norm_mul]
            exact mul_le_mul (hf' _) (he hN _ hw (List.isChain_cons.mp hr).2) (norm_nonneg _) hF
        · rw [norm_mul, hlen]
          exact mul_le_mul_of_nonneg_left (hg _ (by simp [hw])) (norm_nonneg _)
      · rw [norm_mul]
        refine (mul_le_mul_of_nonneg_right (norm_inv_root_le hN) (norm_nonneg _)).trans ?_
        rw [one_mul, norm_mul, hlen]
        exact mul_le_mul_of_nonneg_left (hh _ (by simp [hw])) (norm_nonneg _)

-- Reflecting walks at height −1 subtracts an adjacent binomial coefficient.
private lemma walks_eq (p h : ℕ) : walks p h =
    if (p + h) % 2 = 0 then
      (p.choose ((p + h) / 2) : ℂ) - p.choose ((p + h) / 2 + 1) else 0 := by
  induction p generalizing h with
  | zero =>
    cases h with
    | zero => simp [walks]
    | succ h =>
      simp only [walks, Nat.succ_ne_zero, ite_false, Nat.zero_add]
      split_ifs with he
      · have hpos : 0 < (h + 1) / 2 := by omega
        simp [Nat.choose_eq_zero_of_lt hpos]
      · rfl
  | succ p ih =>
    cases h with
    | zero =>
      rw [walks, ih]
      simp only [Nat.add_zero]
      split_ifs with he
      · let m := p / 2
        have hp : p = 2 * m + 1 := by dsimp [m]; omega
        have hm : (p + 1) / 2 = m + 1 := by omega
        rw [hm, Nat.choose_succ_succ', Nat.choose_succ_succ', Nat.cast_add, Nat.cast_add]
        have hsym : p.choose (m + 1) = p.choose m := hp ▸ Nat.choose_symm_half m
        rw [hsym]
        ring
      · rfl
    | succ h =>
      rw [walks, ih, ih]
      by_cases he : (p + h) % 2 = 0
      · simp only [ite_eq_left he, ite_eq_left (show (p + (h + 2)) % 2 = 0 by omega),
          ite_eq_left (show (p + 1 + (h + 1)) % 2 = 0 by omega)]
        let m := (p + h) / 2
        have h₁ : (p + (h + 2)) / 2 = m + 1 := by dsimp [m]; omega
        have h₂ : (p + 1 + (h + 1)) / 2 = m + 1 := by dsimp [m]; omega
        rw [h₁, h₂, Nat.choose_succ_succ', Nat.choose_succ_succ', Nat.cast_add, Nat.cast_add]
        change _ + ((p.choose m : ℂ) - _) = _
        ring
      · simp only [ite_eq_right he, ite_eq_right (show (p + (h + 2)) % 2 ≠ 0 by omega),
          ite_eq_right (show (p + 1 + (h + 1)) % 2 ≠ 0 by omega), add_zero]

private lemma walks_zero (p : ℕ) :
    walks p 0 =
      (Fintype.card {P : _root_.NoncrossingPartition p // IsPairPartition P.val} : ℂ) := by
  rw [walks_eq, card_noncrossing_pairPartition, Nat.add_zero]
  split_ifs with he
  · let m := p / 2
    have hp : p = 2 * m := by dsimp [m]; omega
    have h₁ := Nat.choose_succ_right_eq p m
    rw [show p - m = m by omega] at h₁
    have h₂ := succ_mul_catalan_eq_centralBinom m
    rw [Nat.centralBinom_eq_two_mul_choose, ← hp] at h₂
    have h : p.choose m = p.choose (m + 1) + catalan m := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m)
      nlinarith
    change (p.choose m : ℂ) - p.choose (m + 1) = catalan m
    rw [h, Nat.cast_add]
    ring
  · simp

private lemma moment_tendsto (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : ℕ → A)
    (hf : AreFree φ hφ a) (hm : ∀ i, φ (a i) = 0) (hv : ∀ i, φ (a i ^ 2) = 1)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C) (p : ℕ) :
    Tendsto (fun N => φ (normalized a N ^ p)) atTop (𝓝 (walks p 0)) := by
  obtain ⟨C, _, hc⟩ := error_bounded φ hφ a hf hm hv hbdd p []
  have hlim : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹ * C) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).mul_const C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h := hc hN ([] : Word N) rfl .nil
  simp only [error, moment, List.length_nil, pow_zero, evalWord, mass, List.map_nil,
    List.prod_nil, mul_one, one_mul, norm_mul, root, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mpr h

end MathlibExt.Probability.FreeProbabilityWanted.free_central_limit

namespace MathlibExt.Probability.FreeProbabilityWanted

open free_central_limit

variable {A : Type*} [Ring A] [Algebra ℂ A]

set_option linter.unusedVariables false in
/-- **The free central limit theorem** (Anderson, Guionnet and Zeitouni, *An Introduction to Random
Matrices*, Lemma 5.3.32). Let `(A, φ)` be a noncommutative probability space with a tracial state:
`φ` is linear, `φ 1 = 1`, `φ (x y) = φ (y x)` and `φ (x⋆ x) ≥ 0`. Let `a₀, a₁, …` be free
self-adjoint elements with `φ aᵢ = 0`, `φ (aᵢ²) = 1` and `sup_i |φ (aᵢᵏ)| < ∞` for every `k`.
Then `X_N = N^{-1/2} (a₀ + ⋯ + a_{N-1})` converges in moments to the standard semicircle law:
for every `p`, `φ (X_Nᵖ)` tends to the number of noncrossing pair partitions of `{1, …, p}`,
which is the `p`-th moment of the semicircle law. -/
public theorem free_central_limit [StarRing A] [StarModule ℂ A] (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1)
    (htrace : ∀ x y, φ (x * y) = φ (y * x)) (hpos : ∀ x, 0 ≤ φ (star x * x))
    (a : ℕ → A) (hfree : AreFree φ hφ a) (hsa : ∀ i, IsSelfAdjoint (a i))
    (hmean : ∀ i, φ (a i) = 0) (hvar : ∀ i, φ (a i ^ 2) = 1)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C) (p : ℕ) :
    Tendsto (fun N : ℕ => φ (((((Real.sqrt N)⁻¹ : ℝ) : ℂ) • ∑ i ∈ Finset.range N, a i) ^ p))
      atTop (𝓝 (Fintype.card {P : _root_.NoncrossingPartition p // IsPairPartition P.val} : ℂ)) :=
  by
    simpa only [normalized, root, Complex.ofReal_inv, Fin.sum_univ_eq_sum_range, walks_zero]
      using moment_tendsto φ hφ a hfree hmean hvar hbdd p

end MathlibExt.Probability.FreeProbabilityWanted
