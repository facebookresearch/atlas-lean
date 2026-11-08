/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Computability.Reduce
import Mathlib.Data.Int.Star

@[expose] public section

namespace MetaMathlibExt

/-! # Weighted r-generalized Fibonacci Binet
-/

private theorem a_nonneg_aux
    (r : ℕ)
    (A c : Fin r → ℝ)
    (hA : ∀ k, 0 ≤ A k)
    (hc : ∀ k, 0 ≤ c k)
    (a : ℕ → ℝ)
    (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
    (ha_rec : ∀ n, r ≤ n →
      a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val))) :
    ∀ n, 0 ≤ a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < r
    · rw [ha_init n h]; exact hc _
    · have hle : r ≤ n := by omega
      rw [ha_rec n hle]
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (hA k) (ih _ (by omega))

private theorem summand_deg_lt
    (r : ℕ) (hr : 2 ≤ r)
    (A : Fin r → ℝ)
    (k : Fin r) :
    (Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val) : Polynomial ℝ).natDegree < r := by
  by_cases hA0 : A k = 0
  · rw [hA0]
    simp
    omega
  · rw [Polynomial.natDegree_mul (by simp [hA0]) (by simp)]
    simp [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X]
    have hk : k.val < r := k.isLt
    omega

/-- The normalized weights `B k = A k / lam ^ (k+1)` sum to one. This is the
characteristic equation `p.eval lam = 0` divided through by `lam ^ r`. -/
private theorem B_sum_eq_one
    (r : ℕ)
    (A : Fin r → ℝ)
    (p : Polynomial ℝ)
    (hp : p = Polynomial.X ^ r -
      Finset.sum Finset.univ (fun k : Fin r =>
        Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val)))
    (lam : ℝ)
    (hlam_pos : 0 < lam)
    (hlam_root : p.IsRoot lam) :
    Finset.sum Finset.univ (fun k : Fin r => A k / lam ^ (k.val + 1)) = 1 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlamr : lam ^ r ≠ 0 := pow_ne_zero r hlam_ne
  have heval : p.eval lam = 0 := hlam_root
  rw [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_finsetSum] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  have hsum : Finset.sum Finset.univ (fun k : Fin r => A k * lam ^ (r - 1 - k.val))
      = lam ^ r := by
    have := sub_eq_zero.mp heval
    simpa [sub_eq_zero] using this.symm
  have hterm : ∀ k : Fin r,
      A k / lam ^ (k.val + 1) = (A k * lam ^ (r - 1 - k.val)) / lam ^ r := by
    intro k
    have hk : k.val < r := k.isLt
    have hkn : (r - 1 - k.val) + (k.val + 1) = r := by omega
    rw [div_eq_div_iff (pow_ne_zero _ hlam_ne) hlamr, mul_assoc, ← pow_add, hkn]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, hsum,
    div_self hlamr]

/-- The rescaled sequence `b n = a n / lam ^ n` is nonnegative. -/
private theorem b_nonneg_thm
    (r : ℕ)
    (A c : Fin r → ℝ)
    (hA : ∀ k, 0 ≤ A k)
    (hc : ∀ k, 0 ≤ c k)
    (a : ℕ → ℝ)
    (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
    (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
    (lam : ℝ)
    (hlam_pos : 0 < lam) :
    ∀ n, 0 ≤ a n / lam ^ n := by
  intro n
  exact div_nonneg
    (a_nonneg_aux r A c hA hc a ha_init ha_rec n)
    (le_of_lt (pow_pos hlam_pos n))

/-- The rescaled sequence satisfies the averaged recurrence
`b n = ∑ B k * b (n - 1 - k)`. -/
private theorem b_rec_thm
    (r : ℕ)
    (A : Fin r → ℝ)
    (a : ℕ → ℝ)
    (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
    (lam : ℝ)
    (hlam_pos : 0 < lam) :
    ∀ n, r ≤ n → a n / lam ^ n =
      Finset.sum Finset.univ (fun k : Fin r =>
        (A k / lam ^ (k.val + 1)) * (a (n - 1 - k.val) / lam ^ (n - 1 - k.val))) := by
  intro n hn
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  rw [ha_rec n hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k.val < r := k.isLt
  have hkn : k.val + 1 + (n - 1 - k.val) = n := by omega
  have hlamn : lam ^ n = lam ^ (k.val + 1) * lam ^ (n - 1 - k.val) := by
    rw [← pow_add, hkn]
  rw [hlamn, div_mul_div_comm]

/-- The rescaled sequence converges to a positive limit. -/
private theorem key_convergence
    (r : ℕ) (hr : 2 ≤ r)
    (A c : Fin r → ℝ)
    (hA : ∀ k, 0 ≤ A k)
    (hc : ∀ k, 0 ≤ c k)
    (hAr : ∃ i : Fin r, i.val + 1 = r ∧ 0 < A i)
    (hcpos : ∃ k₀, 0 < c k₀)
    (hgcd : ∀ d : ℕ, (∀ k : Fin r, 0 < A k → d ∣ k.val + 1) → d = 1)
    (a : ℕ → ℝ)
    (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
    (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
    (p : Polynomial ℝ)
    (hp : p = Polynomial.X ^ r -
      Finset.sum Finset.univ (fun k : Fin r =>
        Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val)))
    (lam : ℝ)
    (hlam_pos : 0 < lam)
    (hlam_root : p.IsRoot lam) :
    ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto (fun n => a n / lam ^ n) Filter.atTop (nhds C) := by
  have hB_nonneg : ∀ k : Fin r, 0 ≤ A k / lam ^ (k.val + 1) := fun k =>
    div_nonneg (hA k) (le_of_lt (pow_pos hlam_pos _))
  have hB_sum : Finset.sum Finset.univ (fun k : Fin r => A k / lam ^ (k.val + 1)) = 1 :=
    B_sum_eq_one r A p hp lam hlam_pos hlam_root
  have hb_rec : ∀ n, r ≤ n → a n / lam ^ n =
      Finset.sum Finset.univ (fun k : Fin r =>
        (A k / lam ^ (k.val + 1)) * (a (n - 1 - k.val) / lam ^ (n - 1 - k.val))) :=
    b_rec_thm r A a ha_rec lam hlam_pos
  -- Sliding windows of `r` consecutive rescaled values and their extrema.
  set W : ℕ → Finset ℝ :=
    fun n => Finset.image (fun j => a j / lam ^ j) (Finset.Ico n (n + r)) with hW
  have hWne : ∀ n, (W n).Nonempty := by
    intro n
    exact ⟨_, Finset.mem_image.mpr
      ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, rfl⟩⟩
  set Mx : ℕ → ℝ := fun n => (W n).max' (hWne n) with hMx
  set mn : ℕ → ℝ := fun n => (W n).min' (hWne n) with hmn
  have hmem : ∀ n j, n ≤ j → j < n + r → a j / lam ^ j ∈ W n := by
    intro n j h1 h2
    rw [hW]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨h1, h2⟩, rfl⟩
  have hleMx : ∀ n j, n ≤ j → j < n + r → a j / lam ^ j ≤ Mx n :=
    fun n j h1 h2 => Finset.le_max' _ _ (hmem n j h1 h2)
  have hmnle : ∀ n j, n ≤ j → j < n + r → mn n ≤ a j / lam ^ j :=
    fun n j h1 h2 => Finset.min'_le _ _ (hmem n j h1 h2)
  -- Every future value stays inside the current window's range.
  have hfut_le : ∀ W0 m, W0 ≤ m → a m / lam ^ m ≤ Mx W0 := by
    intro W0 m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hcase : m < W0 + r
      · exact hleMx W0 m hm hcase
      · have hW0r : r ≤ m := by omega
        rw [hb_rec m hW0r]
        have hterm : ∀ k : Fin r,
            (A k / lam ^ (k.val + 1)) * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val))
              ≤ (A k / lam ^ (k.val + 1)) * Mx W0 := by
          intro k
          have hk : k.val < r := k.isLt
          apply mul_le_mul_of_nonneg_left _ (hB_nonneg k)
          exact ih _ (by omega) (by omega)
        calc Finset.sum Finset.univ (fun k : Fin r =>
                (A k / lam ^ (k.val + 1)) * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val)))
              ≤ Finset.sum Finset.univ (fun k : Fin r => (A k / lam ^ (k.val + 1)) * Mx W0) :=
                Finset.sum_le_sum (fun k _ => hterm k)
          _ = Mx W0 := by rw [← Finset.sum_mul, hB_sum, one_mul]
  have hfut_ge : ∀ W0 m, W0 ≤ m → mn W0 ≤ a m / lam ^ m := by
    intro W0 m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hcase : m < W0 + r
      · exact hmnle W0 m hm hcase
      · have hW0r : r ≤ m := by omega
        rw [hb_rec m hW0r]
        have hterm : ∀ k : Fin r,
            (A k / lam ^ (k.val + 1)) * mn W0
              ≤ (A k / lam ^ (k.val + 1)) * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val)) := by
          intro k
          have hk : k.val < r := k.isLt
          apply mul_le_mul_of_nonneg_left _ (hB_nonneg k)
          exact ih _ (by omega) (by omega)
        calc mn W0 = mn W0 * 1 := by rw [mul_one]
          _ = mn W0 * Finset.sum Finset.univ (fun k : Fin r => A k / lam ^ (k.val + 1)) := by
              rw [hB_sum]
          _ = Finset.sum Finset.univ (fun k : Fin r => mn W0 * (A k / lam ^ (k.val + 1))) := by
              rw [Finset.mul_sum]
          _ = Finset.sum Finset.univ (fun k : Fin r => (A k / lam ^ (k.val + 1)) * mn W0) := by
              apply Finset.sum_congr rfl; intro k _; rw [mul_comm]
          _ ≤ Finset.sum Finset.univ (fun k : Fin r =>
                (A k / lam ^ (k.val + 1)) * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val))) :=
              Finset.sum_le_sum (fun k _ => hterm k)
  -- Window extrema are monotone.
  have hMx_anti : Antitone Mx := by
    apply antitone_nat_of_succ_le
    intro n
    apply Finset.max'_le
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (by rwa [hW] at hy)
    rw [Finset.mem_Ico] at hj
    by_cases hjn : j < n + r
    · exact hleMx n j (by omega) hjn
    · have hjj : j = n + r := by omega
      rw [hjj]
      exact hfut_le n (n + r) (by omega)
  have hmn_mono : Monotone mn := by
    apply monotone_nat_of_le_succ
    intro n
    apply Finset.le_min'
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (by rwa [hW] at hy)
    rw [Finset.mem_Ico] at hj
    by_cases hjn : j < n + r
    · exact hmnle n j (by omega) hjn
    · have hjj : j = n + r := by omega
      rw [hjj]
      exact hfut_ge n (n + r) (by omega)
  have hM_bdd : BddBelow (Set.range Mx) := by
    refine ⟨mn 0, ?_⟩
    rintro _ ⟨W0, rfl⟩
    exact le_trans (hfut_ge 0 W0 (Nat.zero_le _)) (hleMx W0 W0 le_rfl (by omega))
  have hm_bdd : BddAbove (Set.range mn) := by
    refine ⟨Mx 0, ?_⟩
    rintro _ ⟨W0, rfl⟩
    exact le_trans (hmnle W0 W0 le_rfl (by omega)) (hfut_le 0 W0 (Nat.zero_le _))
  have hM_lim : Filter.Tendsto Mx Filter.atTop (nhds (⨅ n, Mx n)) :=
    tendsto_atTop_ciInf hMx_anti hM_bdd
  have hm_lim : Filter.Tendsto mn Filter.atTop (nhds (⨆ n, mn n)) :=
    tendsto_atTop_ciSup hmn_mono hm_bdd
  -- Delays with positive weight.
  set S : Finset ℕ := Finset.image (fun k : Fin r => k.val + 1)
    (Finset.univ.filter (fun k : Fin r => 0 < A k)) with hS
  have hSmem : ∀ s : ℕ, s ∈ S ↔ ∃ k : Fin r, 0 < A k ∧ k.val + 1 = s := by
    intro s
    constructor
    · intro hs
      rw [hS, Finset.mem_image] at hs
      obtain ⟨k, hk, hkk⟩ := hs
      rw [Finset.mem_filter] at hk
      exact ⟨k, hk.2, hkk⟩
    · rintro ⟨k, hk, rfl⟩
      rw [hS, Finset.mem_image]
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, rfl⟩
  obtain ⟨iS, hiS_eq, hiS_pos⟩ := hAr
  have hrS : r ∈ S := by
    rw [hSmem]
    exact ⟨iS, hiS_pos, hiS_eq⟩
  have hSne : S.Nonempty := ⟨r, hrS⟩
  have hSpos : ∀ s ∈ S, 1 ≤ s := by
    intro s hs
    rw [hSmem] at hs
    obtain ⟨k, _, hks⟩ := hs
    omega
  -- The fold of `Nat.gcd` over the delays divides every delay, hence equals 1.
  have : Std.Commutative Nat.gcd := ⟨Nat.gcd_comm⟩
  have : Std.Associative Nat.gcd := ⟨Nat.gcd_assoc⟩
  have hGdiv : ∀ T : Finset ℕ, ∀ s ∈ T, Finset.fold Nat.gcd 0 id T ∣ s := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro s hs
      simp at hs
    · intro b T hbt ih s hs
      rw [Finset.mem_insert] at hs
      have hfold : Finset.fold Nat.gcd 0 id (insert b T)
          = Nat.gcd b (Finset.fold Nat.gcd 0 id T) := by
        simp
      cases hs with
      | inl h => rw [h, hfold]; exact Nat.gcd_dvd_left _ _
      | inr h => rw [hfold]; exact dvd_trans (Nat.gcd_dvd_right _ _) (ih s h)
  have hG1 : Finset.fold Nat.gcd 0 id S = 1 := by
    apply hgcd
    intro k hk
    have hmem : k.val + 1 ∈ S := by
      rw [hSmem]
      exact ⟨k, hk, rfl⟩
    exact hGdiv S _ hmem
  -- Bezout: 1 is an integer combination of the delays.
  have hbez : ∃ z : ℕ → ℤ, (∑ s ∈ S, z s * (s : ℤ)) = 1 := by
    have hmain : ∀ T : Finset ℕ,
        ∃ z : ℕ → ℤ, (∑ s ∈ T, z s * (s : ℤ))
          = ((Finset.fold Nat.gcd 0 id T : ℕ) : ℤ) := by
      intro T
      refine Finset.induction_on T ?_ ?_
      · exact ⟨fun _ => 0, by simp [Finset.fold_empty]⟩
      · intro b T hbt ih
        obtain ⟨z, hz⟩ := ih
        set gT : ℕ := Finset.fold Nat.gcd 0 id T with hgT
        have hfold : Finset.fold Nat.gcd 0 id (insert b T) = Nat.gcd b gT := by
          rw [hgT]
          exact Finset.fold_insert hbt
        have hpair := Nat.gcd_eq_gcd_ab b gT
        refine ⟨Function.update (fun s => Nat.gcdB b gT * z s) b
          (Nat.gcdA b gT), ?_⟩
        have hsumT : (∑ s ∈ T, Function.update (fun s => Nat.gcdB b gT * z s) b
            (Nat.gcdA b gT) s * (s : ℤ)) = Nat.gcdB b gT * ((gT : ℕ) : ℤ) := by
          have hif : ∀ s ∈ T, Function.update (fun s => Nat.gcdB b gT * z s) b
              (Nat.gcdA b gT) s * (s : ℤ)
              = Nat.gcdB b gT * (z s * (s : ℤ)) := by
            intro s hs
            have hsne : s ≠ b := fun h => hbt (h ▸ hs)
            rw [Function.update_of_ne hsne]
            ring
          rw [Finset.sum_congr rfl hif, ← Finset.mul_sum, hz]
        rw [Finset.sum_insert hbt, Function.update_self, hsumT, hfold, hpair]
        ring
    obtain ⟨z, hz⟩ := hmain S
    exact ⟨z, by rw [hG1, Nat.cast_one] at hz; exact hz⟩
  obtain ⟨z, hz⟩ := hbez
  set m0 : ℕ := S.min' hSne with hm0
  have hm0S : m0 ∈ S := Finset.min'_mem S hSne
  have hm0pos : 0 < m0 := by
    have h1 := hSpos m0 hm0S
    omega
  have hm0ne : ((m0 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hm0pos
  set total : ℕ := ∑ s ∈ S, s with htotal
  set N0 : ℕ := m0 * total with hN0
  -- Frobenius coin problem: every large `n` is a nonnegative combination.
  have hfrob : ∀ n : ℕ, N0 ≤ n → ∃ w : ℕ → ℕ, n = ∑ s ∈ S, w s * s := by
    intro n hn
    set q : ℕ → ℤ := fun s => ((n : ℤ) * z s) / ((m0 : ℕ) : ℤ) with hq
    set t : ℕ → ℤ := fun s => ((n : ℤ) * z s) % ((m0 : ℕ) : ℤ) with ht
    have hqt : ∀ s ∈ S, (m0 : ℤ) * q s + t s = (n : ℤ) * z s := fun s _ =>
      Int.mul_ediv_add_emod _ _
    have ht_nonneg : ∀ s ∈ S, 0 ≤ t s := fun s _ => Int.emod_nonneg _ hm0ne
    have ht_lt : ∀ s ∈ S, t s < (m0 : ℤ) := by
      intro s _
      have h := Int.emod_lt ((n : ℤ) * z s) hm0ne
      have h2 : ((((m0 : ℕ) : ℤ)).natAbs : ℤ) = ((m0 : ℕ) : ℤ) :=
        Int.natAbs_of_nonneg (by positivity)
      rwa [h2] at h
    set Q : ℤ := ∑ s ∈ S, q s * (s : ℤ) with hQ
    have hQm0 : (m0 : ℤ) * Q = (n : ℤ) - ∑ s ∈ S, t s * (s : ℤ) := by
      have e1 : (∑ s ∈ S, (m0 : ℤ) * (q s * (s : ℤ)))
          = ∑ s ∈ S, (((n : ℤ) * z s - t s) * (s : ℤ)) := by
        apply Finset.sum_congr rfl
        intro s hs
        have h := hqt s hs
        have h2 : q s * (m0 : ℤ) = (n : ℤ) * z s - t s := by linarith [h]
        calc (m0 : ℤ) * (q s * (s : ℤ)) = (q s * (m0 : ℤ)) * (s : ℤ) := by ring
          _ = (((n : ℤ) * z s - t s) * (s : ℤ)) := by rw [h2]
      have e2 : (∑ s ∈ S, (((n : ℤ) * z s - t s) * (s : ℤ)))
          = (n : ℤ) - ∑ s ∈ S, t s * (s : ℤ) := by
        have e3 : (∑ s ∈ S, (((n : ℤ) * z s)) * (s : ℤ)) = (n : ℤ) := by
          have e3a : (∑ s ∈ S, (((n : ℤ) * z s)) * (s : ℤ))
              = (n : ℤ) * (∑ s ∈ S, z s * (s : ℤ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
          rw [e3a, hz, mul_one]
        calc (∑ s ∈ S, (((n : ℤ) * z s - t s) * (s : ℤ)))
            = (∑ s ∈ S, (((n : ℤ) * z s)) * (s : ℤ)) - (∑ s ∈ S, t s * (s : ℤ)) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro s _
              rw [sub_mul]
          _ = (n : ℤ) - ∑ s ∈ S, t s * (s : ℤ) := by rw [e3]
      rw [hQ, Finset.mul_sum]
      exact e1.trans e2
    have hle : (∑ s ∈ S, t s * (s : ℤ))
        ≤ (((m0 : ℕ) : ℤ) - 1) * ((total : ℕ) : ℤ) := by
      have estep : (∑ s ∈ S, t s * (s : ℤ))
          ≤ ∑ s ∈ S, ((((m0 : ℕ) : ℤ) - 1) * (s : ℤ)) := by
        apply Finset.sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h := ht_lt s hs
        omega
      calc (∑ s ∈ S, t s * (s : ℤ))
          ≤ ∑ s ∈ S, ((((m0 : ℕ) : ℤ) - 1) * (s : ℤ)) := estep
        _ = ((((m0 : ℕ) : ℤ) - 1)) * ((total : ℕ) : ℤ) := by
            rw [htotal, Nat.cast_sum, ← Finset.mul_sum]
    have hnI : ((m0 : ℤ)) * ((total : ℕ) : ℤ) ≤ (n : ℤ) := by
      have hcast : ((N0 : ℕ) : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast hn
      rwa [hN0, Nat.cast_mul] at hcast
    have hQnn : 0 ≤ Q := by
      have htot_nn : (0 : ℤ) ≤ ((total : ℕ) : ℤ) := by positivity
      have h3 : (((m0 : ℕ) : ℤ) - 1) * ((total : ℕ) : ℤ)
          = (m0 : ℤ) * ((total : ℕ) : ℤ) - ((total : ℕ) : ℤ) := by ring
      have hm0Q : (0 : ℤ) ≤ (m0 : ℤ) * Q := by
        rw [hQm0]
        omega
      by_contra hneg
      push Not at hneg
      have hlt : (m0 : ℤ) * Q < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hm0pos) hneg
      omega
    refine ⟨Function.update (fun s => (t s).toNat) m0 (Q.toNat + (t m0).toNat), ?_⟩
    have eQ : (Q.toNat : ℤ) = Q := Int.toNat_of_nonneg hQnn
    have et : ∀ s ∈ S, (((t s).toNat : ℕ) : ℤ) = t s := fun s hs =>
      Int.toNat_of_nonneg (ht_nonneg s hs)
    have hsumI : (∑ s ∈ S, ((Function.update (fun s => (t s).toNat) m0
        (Q.toNat + (t m0).toNat) s : ℕ) : ℤ) * (s : ℤ)) = (n : ℤ) := by
      rw [← Finset.add_sum_erase _ _ hm0S]
      simp only [Function.update_self]
      have erest : (∑ x ∈ S.erase m0, ((Function.update (fun s => (t s).toNat) m0
          (Q.toNat + (t m0).toNat) x : ℕ) : ℤ) * (x : ℤ))
          = ∑ x ∈ S.erase m0, t x * (x : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxne : x ≠ m0 := Finset.ne_of_mem_erase hx
        rw [Function.update_of_ne hxne]
        change (((t x).toNat : ℕ) : ℤ) * (x : ℤ) = t x * (x : ℤ)
        rw [et x (Finset.mem_of_mem_erase hx)]
      rw [erest]
      rw [Nat.cast_add, eQ, et m0 hm0S]
      have hcomb : t m0 * (m0 : ℤ) + ∑ x ∈ S.erase m0, t x * (x : ℤ)
          = ∑ s ∈ S, t s * (s : ℤ) :=
        Finset.add_sum_erase S (fun s => t s * (s : ℤ)) hm0S
      have hexpand : (Q + t m0) * (m0 : ℤ) + ∑ x ∈ S.erase m0, t x * (x : ℤ)
          = (m0 : ℤ) * Q + (∑ s ∈ S, t s * (s : ℤ)) := by
        rw [← hcomb]; ring
      rw [hexpand, hQm0, sub_add_cancel]
    have hfinal : n = ∑ s ∈ S, Function.update (fun s => (t s).toNat) m0
        (Q.toNat + (t m0).toNat) s * s := by
      have hcast : ((∑ s ∈ S, Function.update (fun s => (t s).toNat) m0
          (Q.toNat + (t m0).toNat) s * s : ℕ) : ℤ) = ((n : ℕ) : ℤ) := by
        calc ((∑ s ∈ S, Function.update (fun s => (t s).toNat) m0
              (Q.toNat + (t m0).toNat) s * s : ℕ) : ℤ)
            = ∑ s ∈ S, ((Function.update (fun s => (t s).toNat) m0
              (Q.toNat + (t m0).toNat) s : ℕ) : ℤ) * (s : ℤ) := by
              rw [Nat.cast_sum]
              apply Finset.sum_congr rfl
              intro s _
              rw [Nat.cast_mul]
          _ = ((n : ℕ) : ℤ) := hsumI
      exact (Nat.cast_inj.mp hcast).symm
    exact hfinal
  -- Delay lists realizing each large integer.
  have hlist : ∀ D : ℕ, N0 ≤ D → ∃ L : List ℕ,
      (∀ s ∈ L, s ∈ S) ∧ L.sum = D := by
    intro D hD
    obtain ⟨w, hw⟩ := hfrob D hD
    have hbuild : ∀ T : Finset ℕ, T ⊆ S → ∃ L : List ℕ,
        (∀ s ∈ L, s ∈ S) ∧ L.sum = ∑ s ∈ T, w s * s := by
      intro T
      refine Finset.induction_on T ?_ ?_
      · intro _
        exact ⟨[], by simp, by simp⟩
      · intro b T hbt ih hsub
        obtain ⟨L, hLmem, hLsum⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
        refine ⟨List.replicate (w b) b ++ L, ?_, ?_⟩
        · intro x hx
          rw [List.mem_append] at hx
          cases hx with
          | inl h =>
            rw [List.mem_replicate] at h
            obtain ⟨-, hxb⟩ := h
            rw [hxb]
            exact hsub (Finset.mem_insert_self b T)
          | inr h => exact hLmem x h
        · rw [List.sum_append, List.sum_replicate, nsmul_eq_mul, hLsum,
            Finset.sum_insert hbt, Nat.cast_id]
    obtain ⟨L, hLmem, hLsum⟩ := hbuild S Finset.Subset.rfl
    exact ⟨L, hLmem, hLsum.trans hw.symm⟩
  -- Positive weight for each delay.
  have hBpos : ∀ s ∈ S, ∃ k : Fin r, 0 < A k ∧ k.val + 1 = s ∧
      0 < A k / lam ^ (k.val + 1) := by
    intro s hs
    rw [hSmem] at hs
    obtain ⟨k, hk, hks⟩ := hs
    exact ⟨k, hk, hks, div_pos hk (pow_pos hlam_pos _)⟩
  set P : Finset ℝ := Finset.image (fun k : Fin r => A k / lam ^ (k.val + 1))
    (Finset.univ.filter (fun k : Fin r => 0 < A k)) with hP
  have hPne : P.Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨iS, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hiS_pos⟩, rfl⟩⟩
  set beta : ℝ := P.min' hPne with hbeta
  have hbeta_pos : 0 < beta := by
    have hmem := Finset.min'_mem P hPne
    have hmem2 : P.min' hPne ∈ Finset.image (fun k : Fin r => A k / lam ^ (k.val + 1))
        (Finset.univ.filter (fun k : Fin r => 0 < A k)) := hmem
    rw [Finset.mem_image] at hmem2
    obtain ⟨k, hk, hkk⟩ := hmem2
    rw [Finset.mem_filter] at hk
    change 0 < P.min' hPne
    rw [← hkk]
    exact div_pos hk.2 (pow_pos hlam_pos _)
  set Mstar : ℝ := ⨅ n, Mx n with hMstar
  set mstar : ℝ := ⨆ n, mn n with hmstar
  -- Backward propagation of near-maximality along a delay list.
  have hback : ∀ (L : List ℕ), (∀ s ∈ L, s ∈ S) → ∀ (W : ℕ) (δ e : ℝ) (t m : ℕ),
      0 ≤ δ → 0 ≤ e → Mx W ≤ Mstar + δ → W + r ≤ t → m = t + L.sum →
      Mstar - e ≤ a m / lam ^ m →
      Mstar - (2 / beta) ^ L.length * (e + δ) ≤ a t / lam ^ t := by
    intro L
    induction L with
    | nil =>
      intro hL W δ e t m hδ he hW hWt hm hbm
      rw [List.sum_nil, add_zero] at hm
      subst hm
      rw [List.length_nil, pow_zero, one_mul]
      linarith
    | cons s R ih =>
      intro hL W δ e t m hδ he hW hWt hm hbm
      have hsS : s ∈ S := hL s (List.mem_cons.mpr (Or.inl rfl))
      have hRS : ∀ x ∈ R, x ∈ S := fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))
      obtain ⟨k, hkpos, hks, hBkpos⟩ := hBpos s hsS
      have hBk1 : A k / lam ^ (k.val + 1) ≤ 1 := by
        have h1 : A k / lam ^ (k.val + 1)
            ≤ ∑ j : Fin r, A j / lam ^ (j.val + 1) :=
          Finset.single_le_sum (fun j _ => hB_nonneg j) (Finset.mem_univ k)
        rwa [hB_sum] at h1
      have hBkbeta : beta ≤ A k / lam ^ (k.val + 1) := by
        rw [hbeta]
        apply Finset.min'_le
        rw [hP, Finset.mem_image]
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkpos⟩, rfl⟩
      have hsc : (s :: R).sum = s + R.sum := List.sum_cons
      set m1 : ℕ := m - s with hm1
      have hm1eq : m1 + s = m := by omega
      have hm1ge : W + r ≤ m1 := by omega
      have hmge_r : r ≤ m := by omega
      have hrec := hb_rec m hmge_r
      have hterm : ∀ j : Fin r,
          (A j / lam ^ (j.val + 1)) * (a (m - 1 - j.val) / lam ^ (m - 1 - j.val))
            ≤ (A j / lam ^ (j.val + 1)) * Mx W := by
        intro j
        apply mul_le_mul_of_nonneg_left _ (hB_nonneg j)
        apply hfut_le W
        have hjlt := j.isLt
        omega
      have hsplit : Finset.sum Finset.univ (fun j : Fin r =>
          (A j / lam ^ (j.val + 1)) * (a (m - 1 - j.val) / lam ^ (m - 1 - j.val)))
          ≤ (∑ j ∈ Finset.univ.erase k, (A j / lam ^ (j.val + 1)) * Mx W)
            + (A k / lam ^ (k.val + 1)) * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val)) := by
        have h := Finset.add_sum_erase Finset.univ (fun j : Fin r =>
          (A j / lam ^ (j.val + 1)) * (a (m - 1 - j.val) / lam ^ (m - 1 - j.val)))
          (Finset.mem_univ k)
        have h2 : (∑ j ∈ Finset.univ.erase k, (A j / lam ^ (j.val + 1))
            * (a (m - 1 - j.val) / lam ^ (m - 1 - j.val)))
            ≤ (∑ j ∈ Finset.univ.erase k, (A j / lam ^ (j.val + 1)) * Mx W) :=
          Finset.sum_le_sum (fun j hj => hterm j)
        have h3 : Finset.sum Finset.univ (fun j : Fin r =>
            (A j / lam ^ (j.val + 1)) * (a (m - 1 - j.val) / lam ^ (m - 1 - j.val)))
            = (∑ j ∈ Finset.univ.erase k, (A j / lam ^ (j.val + 1))
              * (a (m - 1 - j.val) / lam ^ (m - 1 - j.val)))
              + (A k / lam ^ (k.val + 1)) * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val)) := by
          rw [← h]
          exact add_comm _ _
        rw [h3]
        exact add_le_add_left h2 ((A k / lam ^ (k.val + 1))
          * (a (m - 1 - k.val) / lam ^ (m - 1 - k.val)))
      have hidx : m - 1 - k.val = m1 := by omega
      have hrest : (∑ j ∈ Finset.univ.erase k, (A j / lam ^ (j.val + 1)) * Mx W)
          = (1 - A k / lam ^ (k.val + 1)) * Mx W := by
        have e1 : (∑ j ∈ Finset.univ.erase k, (A j / lam ^ (j.val + 1)) * Mx W)
            = (∑ j ∈ Finset.univ.erase k, A j / lam ^ (j.val + 1)) * Mx W := by
          rw [← Finset.sum_mul]
        have e2 : (∑ j ∈ Finset.univ.erase k, A j / lam ^ (j.val + 1))
            = 1 - A k / lam ^ (k.val + 1) := by
          have h3 := Finset.add_sum_erase Finset.univ
            (fun j : Fin r => A j / lam ^ (j.val + 1)) (Finset.mem_univ k)
          rw [hB_sum] at h3
          linarith [h3]
        rw [e1, e2]
      have hfin : a m / lam ^ m ≤ (1 - A k / lam ^ (k.val + 1)) * Mx W
          + (A k / lam ^ (k.val + 1)) * (a m1 / lam ^ m1) := by
        rw [hrec]
        rw [hidx] at hsplit
        rw [← hrest]
        exact hsplit
      have hBk_ne : (A k / lam ^ (k.val + 1)) ≠ 0 := ne_of_gt hBkpos
      have hmul : (A k / lam ^ (k.val + 1)) * ((e + δ) / (A k / lam ^ (k.val + 1)))
          = e + δ := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hBk_ne
      have z1 : (1 - A k / lam ^ (k.val + 1)) * Mx W
          ≤ (1 - A k / lam ^ (k.val + 1)) * (Mstar + δ) :=
        mul_le_mul_of_nonneg_left hW (by linarith [hBk1])
      have z2 : Mstar - e - (1 - A k / lam ^ (k.val + 1)) * (Mstar + δ)
          ≤ (A k / lam ^ (k.val + 1)) * (a m1 / lam ^ m1) := by
        linarith [hfin, hbm, z1]
      have z3 : (A k / lam ^ (k.val + 1)) * Mstar - (e + δ)
          ≤ (A k / lam ^ (k.val + 1)) * (a m1 / lam ^ m1) := by
        have hexp : (1 - A k / lam ^ (k.val + 1)) * (Mstar + δ)
            = (Mstar + δ) - (A k / lam ^ (k.val + 1)) * (Mstar + δ) := by ring
        have hBδ : 0 ≤ (A k / lam ^ (k.val + 1)) * δ :=
          mul_nonneg (le_of_lt hBkpos) hδ
        linarith [z2, hexp, hBδ]
      have key : (A k / lam ^ (k.val + 1))
            * (Mstar - (e + δ) / (A k / lam ^ (k.val + 1)))
          ≤ (A k / lam ^ (k.val + 1)) * (a m1 / lam ^ m1) := by
        have hexp2 : (A k / lam ^ (k.val + 1))
              * (Mstar - (e + δ) / (A k / lam ^ (k.val + 1)))
            = (A k / lam ^ (k.val + 1)) * Mstar - (e + δ) := by
          rw [mul_sub, hmul]
        rw [hexp2]
        exact z3
      have hconc : Mstar - (e + δ) / (A k / lam ^ (k.val + 1)) ≤ a m1 / lam ^ m1 :=
        le_of_mul_le_mul_left key hBkpos
      have hm1R : m1 = t + R.sum := by omega
      have he1nn : 0 ≤ (e + δ) / (A k / lam ^ (k.val + 1)) :=
        div_nonneg (add_nonneg he hδ) (le_of_lt hBkpos)
      have hIH := ih hRS W δ ((e + δ) / (A k / lam ^ (k.val + 1))) t m1
        hδ he1nn hW hWt hm1R hconc
      have h1 : ((e + δ) / (A k / lam ^ (k.val + 1))) ≤ (e + δ) / beta :=
        div_le_div_of_nonneg_left (add_nonneg he hδ) hbeta_pos hBkbeta
      have hbeta1 : beta ≤ 1 := le_trans hBkbeta hBk1
      have h2 : δ ≤ (e + δ) / beta := by
        have h2a : (e + δ) / 1 ≤ (e + δ) / beta :=
          div_le_div_of_nonneg_left (add_nonneg he hδ) hbeta_pos hbeta1
        rw [div_one] at h2a
        exact le_trans (by linarith [he]) h2a
      have h3 : ((e + δ) / (A k / lam ^ (k.val + 1))) + δ ≤ (2 / beta) * (e + δ) := by
        have h4 : (2 / beta) * (e + δ) = 2 * ((e + δ) / beta) := by ring
        linarith [h1, h2, h4]
      have hK : (2 / beta) ^ R.length * (((e + δ) / (A k / lam ^ (k.val + 1))) + δ)
          ≤ (2 / beta) ^ (s :: R).length * (e + δ) := by
        rw [List.length_cons]
        calc (2 / beta) ^ R.length * (((e + δ) / (A k / lam ^ (k.val + 1))) + δ)
            ≤ (2 / beta) ^ R.length * ((2 / beta) * (e + δ)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (2 / beta) ^ (R.length + 1) * (e + δ) := by ring
      calc Mstar - (2 / beta) ^ (s :: R).length * (e + δ)
          ≤ Mstar - (2 / beta) ^ R.length
            * (((e + δ) / (A k / lam ^ (k.val + 1))) + δ) := by linarith [hK]
        _ ≤ a t / lam ^ t := hIH
  -- Identify the two limits.
  have hleMM : mstar ≤ Mstar :=
    le_of_tendsto_of_tendsto hm_lim hM_lim
      (Filter.Eventually.of_forall (fun n =>
        le_trans (hmnle n n le_rfl (by omega)) (hleMx n n le_rfl (by omega))))
  have hbeta1 : beta ≤ 1 := by
    have hmem : A iS / lam ^ (iS.val + 1) ∈ P := Finset.mem_image.mpr
      ⟨iS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS_pos⟩, rfl⟩
    have h1 : A iS / lam ^ (iS.val + 1) ≤ 1 := by
      have h2 : A iS / lam ^ (iS.val + 1)
          ≤ ∑ j : Fin r, A j / lam ^ (j.val + 1) :=
        Finset.single_le_sum (fun j _ => hB_nonneg j) (Finset.mem_univ iS)
      rwa [hB_sum] at h2
    have hmin : beta ≤ A iS / lam ^ (iS.val + 1) := by
      rw [hbeta]
      apply Finset.min'_le
      exact hmem
    exact le_trans hmin h1
  set K : ℝ := (2 / beta) ^ (N0 + r) with hK
  have hKpos : 0 < K := pow_pos (div_pos two_pos hbeta_pos) _
  have h2beta : (1 : ℝ) ≤ 2 / beta := by
    rw [le_div_iff₀ hbeta_pos]
    linarith [hbeta1]
  have hlen : ∀ L : List ℕ, (∀ s ∈ L, 1 ≤ s) → L.length ≤ L.sum := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons a l ih =>
      intro h
      have ha : 1 ≤ a := h a (List.mem_cons.mpr (Or.inl rfl))
      have hl : ∀ s ∈ l, 1 ≤ s := fun s hs => h s (List.mem_cons.mpr (Or.inr hs))
      have ihl := ih hl
      rw [List.length_cons, List.sum_cons]
      omega
  have heqMM : Mstar = mstar := by
    apply le_antisymm _ hleMM
    apply le_of_forall_pos_le_add
    intro γ hγ
    set e0 : ℝ := γ / (2 * K + 2) with he0def
    have he0pos : 0 < e0 := by
      rw [he0def]
      apply div_pos hγ
      linarith [hKpos]
    have hKeps : K * (e0 + e0) ≤ γ := by
      have h2K : (0 : ℝ) < 2 * K + 2 := by linarith [hKpos]
      have heq : K * (e0 + e0) = (2 * K * γ) / (2 * K + 2) := by
        rw [he0def]; ring
      rw [heq, div_le_iff₀ h2K]
      linarith [hγ]
    have hlt : Mstar < Mstar + e0 := by linarith [he0pos]
    have hWev : ∀ᶠ n in Filter.atTop, Mx n < Mstar + e0 :=
      hM_lim.eventually (gt_mem_nhds hlt)
    obtain ⟨W0, hW0⟩ := Filter.eventually_atTop.mp hWev
    have hW0le : Mx W0 ≤ Mstar + e0 := le_of_lt (hW0 W0 le_rfl)
    set W2 : ℕ := max W0 (W0 + N0 + 2 * r) with hW2
    have hW2ge : W0 + N0 + 2 * r ≤ W2 := le_max_right _ _
    have hmaxmem : Mx W2 ∈ W W2 := Finset.max'_mem _ _
    have hmaxmem2 : Mx W2 ∈ Finset.image (fun j => a j / lam ^ j)
        (Finset.Ico W2 (W2 + r)) := hmaxmem
    obtain ⟨j, hj, hjj⟩ := Finset.mem_image.mp hmaxmem2
    rw [Finset.mem_Ico] at hj
    have hjge : W0 + N0 + 2 * r ≤ j := le_trans hW2ge hj.1
    have hjmax : Mstar - e0 ≤ a j / lam ^ j := by
      have h1 : Mstar ≤ Mx W2 := ciInf_le hM_bdd W2
      have h2 : Mx W2 = a j / lam ^ j := hjj.symm
      linarith [h1, h2, he0pos]
    set W3 : ℕ := j - N0 - r + 1 with hW3
    have hwindow : ∀ i, W3 ≤ i → i < W3 + r →
        Mstar - K * (e0 + e0) ≤ a i / lam ^ i := by
      intro i hi1 hi2
      set D : ℕ := j - i with hD
      have hDj : D ≤ j := by omega
      have hD1 : N0 ≤ D := by omega
      have hD2 : D < N0 + r := by omega
      have hDrange : D ∈ Finset.Ico N0 (N0 + r) := Finset.mem_Ico.mpr ⟨hD1, hD2⟩
      obtain ⟨L, hLmem, hLsum⟩ := hlist D hD1
      have hDm : j = (j - D) + L.sum := by omega
      have hWtD : W0 + r ≤ j - D := by omega
      have happ := hback L hLmem W0 e0 e0 (j - D) j
        (le_of_lt he0pos) (le_of_lt he0pos) hW0le hWtD hDm hjmax
      have hi_eq : j - D = i := by omega
      rw [hi_eq] at happ
      have hlen_le : L.length ≤ N0 + r :=
        calc L.length ≤ L.sum := hlen L (fun s hs => hSpos s (hLmem s hs))
          _ = D := hLsum
          _ ≤ N0 + r := by omega
      have hKle : (2 / beta) ^ L.length ≤ K := by
        rw [hK]
        exact pow_le_pow_right₀ h2beta hlen_le
      have hmono : (2 / beta) ^ L.length * (e0 + e0) ≤ K * (e0 + e0) :=
        mul_le_mul_of_nonneg_right hKle (le_of_lt (by linarith : (0 : ℝ) < e0 + e0))
      calc Mstar - K * (e0 + e0)
          ≤ Mstar - (2 / beta) ^ L.length * (e0 + e0) := by linarith [hmono]
        _ ≤ a i / lam ^ i := happ
    have hmnW3 : Mstar - K * (e0 + e0) ≤ mn W3 := by
      change Mstar - K * (e0 + e0) ≤ (W W3).min' (hWne W3)
      apply Finset.le_min'
      intro y hy
      have hy2 : y ∈ Finset.image (fun j => a j / lam ^ j)
          (Finset.Ico W3 (W3 + r)) := hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy2
      rw [Finset.mem_Ico] at hi
      exact hwindow i hi.1 hi.2
    have hmstar_ge : Mstar - K * (e0 + e0) ≤ mstar :=
      le_trans hmnW3 (le_ciSup hm_bdd W3)
    linarith [hmstar_ge, hKeps]
  -- Forward propagation of positivity from the positive seed.
  obtain ⟨k0, hk0⟩ := hcpos
  have hk0lt : k0.val < r := k0.isLt
  have hbseed : 0 < a k0.val / lam ^ k0.val := by
    rw [ha_init k0.val hk0lt]
    exact div_pos hk0 (pow_pos hlam_pos _)
  have hstep : ∀ L : List ℕ, (∀ s ∈ L, s ∈ S) → ∀ t : ℕ, k0.val + r ≤ t →
      0 < a t / lam ^ t → 0 < a (t + L.sum) / lam ^ (t + L.sum) := by
    intro L
    induction L with
    | nil =>
      intro hL t ht hpos
      simpa using hpos
    | cons s R ih =>
      intro hL t ht hpos
      rw [List.sum_cons]
      have hsS : s ∈ S := hL s (List.mem_cons.mpr (Or.inl rfl))
      have hRS : ∀ x ∈ R, x ∈ S := fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))
      obtain ⟨k, hkpos, hks, hBkpos⟩ := hBpos s hsS
      have hbase : 0 < a (t + R.sum) / lam ^ (t + R.sum) := ih hRS t ht hpos
      have hidxn : r ≤ t + (s + R.sum) := by omega
      have hrec := hb_rec (t + (s + R.sum)) hidxn
      have hkidx : t + (s + R.sum) - 1 - k.val = t + R.sum := by omega
      have hkk : (A k / lam ^ (k.val + 1)) * (a (t + R.sum) / lam ^ (t + R.sum))
          = (A k / lam ^ (k.val + 1))
            * (a (t + (s + R.sum) - 1 - k.val) / lam ^ (t + (s + R.sum) - 1 - k.val)) := by
        rw [hkidx]
      have hterm : (A k / lam ^ (k.val + 1))
          * (a (t + (s + R.sum) - 1 - k.val) / lam ^ (t + (s + R.sum) - 1 - k.val))
          ≤ a (t + (s + R.sum)) / lam ^ (t + (s + R.sum)) := by
        rw [hrec]
        exact Finset.single_le_sum (fun j _ => mul_nonneg (hB_nonneg j)
          (b_nonneg_thm r A c hA hc a ha_init ha_rec lam hlam_pos
            (t + (s + R.sum) - 1 - j.val)))
          (Finset.mem_univ k)
      calc 0 < (A k / lam ^ (k.val + 1)) * (a (t + R.sum) / lam ^ (t + R.sum)) :=
            mul_pos hBkpos hbase
        _ = (A k / lam ^ (k.val + 1))
            * (a (t + (s + R.sum) - 1 - k.val) / lam ^ (t + (s + R.sum) - 1 - k.val)) := hkk
        _ ≤ a (t + (s + R.sum)) / lam ^ (t + (s + R.sum)) := hterm
  have hbr : 0 < a (k0.val + r) / lam ^ (k0.val + r) := by
    have hrec := hb_rec (k0.val + r) (by omega)
    have hterm : (A iS / lam ^ (iS.val + 1))
        * (a (k0.val + r - 1 - iS.val) / lam ^ (k0.val + r - 1 - iS.val))
        ≤ a (k0.val + r) / lam ^ (k0.val + r) := by
      rw [hrec]
      exact Finset.single_le_sum (fun j _ => mul_nonneg (hB_nonneg j)
        (b_nonneg_thm r A c hA hc a ha_init ha_rec lam hlam_pos
          (k0.val + r - 1 - j.val)))
        (Finset.mem_univ iS)
    have hidx0 : k0.val + r - 1 - iS.val = k0.val := by omega
    rw [hidx0] at hterm
    have hpos0 : 0 < (A iS / lam ^ (iS.val + 1)) * (a k0.val / lam ^ k0.val) :=
      mul_pos (div_pos hiS_pos (pow_pos hlam_pos _)) hbseed
    exact lt_of_lt_of_le hpos0 hterm
  have hpos : ∀ m : ℕ, k0.val + N0 + r ≤ m → 0 < a m / lam ^ m := by
    intro m hm
    have hDge : N0 ≤ m - k0.val - r := by omega
    obtain ⟨L, hLmem, hLsum⟩ := hlist (m - k0.val - r) hDge
    have hmeq : k0.val + r + L.sum = m := by omega
    rw [← hmeq]
    exact hstep L hLmem (k0.val + r) le_rfl hbr
  have hCpos : 0 < mstar := by
    have hWpos : 0 < mn (k0.val + N0 + r) := by
      change 0 < (W (k0.val + N0 + r)).min' (hWne (k0.val + N0 + r))
      have hmem0 := Finset.min'_mem (W (k0.val + N0 + r)) (hWne (k0.val + N0 + r))
      have hmem1 : (W (k0.val + N0 + r)).min' (hWne (k0.val + N0 + r))
          ∈ Finset.image (fun j => a j / lam ^ j)
            (Finset.Ico (k0.val + N0 + r) (k0.val + N0 + r + r)) := hmem0
      obtain ⟨i, hi, hii⟩ := Finset.mem_image.mp hmem1
      rw [Finset.mem_Ico] at hi
      have hpi := hpos i (by omega)
      have hcon : (W (k0.val + N0 + r)).min' (hWne (k0.val + N0 + r))
          = a i / lam ^ i := hii.symm
      rw [hcon]
      exact hpi
    calc (0 : ℝ) < mn (k0.val + N0 + r) := hWpos
      _ ≤ mstar := le_ciSup hm_bdd _
  have hblim : Filter.Tendsto (fun n => a n / lam ^ n) Filter.atTop (nhds mstar) := by
    have h1 : Filter.Tendsto mn Filter.atTop (nhds mstar) := hm_lim
    have h2 : Filter.Tendsto Mx Filter.atTop (nhds mstar) := by
      rw [← heqMM]
      exact hM_lim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2
      (fun n => hmnle n n le_rfl (by omega)) (fun n => hleMx n n le_rfl (by omega))
  exact ⟨mstar, hCpos, hblim⟩

/-- `binet` without the hypotheses `hlam_simple` and `hlam_dom`: a positive root `lam` of the
characteristic polynomial already gives the asymptotics and the ratio limit. -/
theorem binet_general
    (r : ℕ) (hr : 2 ≤ r)
    (A c : Fin r → ℝ)
    (hA : ∀ k, 0 ≤ A k)
    (hc : ∀ k, 0 ≤ c k)
    (hAr : ∃ i : Fin r, i.val + 1 = r ∧ 0 < A i)
    (hcpos : ∃ k₀, 0 < c k₀)
    (hgcd : ∀ d : ℕ, (∀ k : Fin r, 0 < A k → d ∣ k.val + 1) → d = 1)
    (a : ℕ → ℝ)
    (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
    (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
    (p : Polynomial ℝ)
    (hp : p = Polynomial.X ^ r -
      Finset.sum Finset.univ (fun k : Fin r =>
        Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val)))
    (lam : ℝ)
    (hlam_pos : 0 < lam)
    (hlam_root : p.IsRoot lam) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsLittleO Filter.atTop (fun n => a n - C * lam ^ n)
        (fun n => lam ^ n) ∧
      Filter.Tendsto (fun n => a (n + 1) / a n) Filter.atTop (nhds lam) := by
  obtain ⟨C, hC, hlim⟩ := key_convergence r hr A c hA hc hAr hcpos hgcd a
    ha_init ha_rec p hp lam hlam_pos hlam_root
  have hlam_ne : ∀ n : ℕ, lam ^ n ≠ 0 := fun n => pow_ne_zero n (ne_of_gt hlam_pos)
  have hlam0 : lam ≠ 0 := ne_of_gt hlam_pos
  refine ⟨C, hC, ?_, ?_⟩
  · -- Little-o from convergence of the rescaled sequence.
    rw [Asymptotics.isLittleO_iff_tendsto (fun n hn => absurd hn (hlam_ne n))]
    have heq : (fun n => (a n - C * lam ^ n) / lam ^ n)
        = (fun n => a n / lam ^ n - C) := by
      apply funext
      intro n
      rw [sub_div, mul_div_cancel_right₀ _ (hlam_ne n)]
    rw [heq]
    have hsub := hlim.sub_const C
    rwa [sub_self] at hsub
  · -- Ratio limit from the rescaled limit.
    have hshift : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      exact Filter.eventually_ge_atTop b |>.mono
        (fun n hn => le_trans hn (Nat.le_add_right n 1))
    have hb1 : Filter.Tendsto (fun n => a (n + 1) / lam ^ (n + 1)) Filter.atTop
        (nhds C) :=
      hlim.comp hshift
    have hdiv : Filter.Tendsto
        (fun n => (a (n + 1) / lam ^ (n + 1)) / (a n / lam ^ n)) Filter.atTop
        (nhds (C / C)) :=
      Filter.Tendsto.div hb1 hlim (ne_of_gt hC)
    rw [div_self (ne_of_gt hC)] at hdiv
    have hmul : Filter.Tendsto
        (fun n => lam * ((a (n + 1) / lam ^ (n + 1)) / (a n / lam ^ n)))
        Filter.atTop (nhds (lam * 1)) :=
      Filter.Tendsto.const_mul lam hdiv
    rw [mul_one] at hmul
    have heq : (fun n => a (n + 1) / a n)
        = (fun n => lam * ((a (n + 1) / lam ^ (n + 1)) / (a n / lam ^ n))) := by
      apply funext
      intro n
      by_cases hA0 : a n = 0
      · rw [hA0]
        simp [pow_succ]
      · have hLn : lam ^ n ≠ 0 := hlam_ne n
        rw [pow_succ]
        field_simp
    rw [heq]
    exact hmul

set_option linter.unusedVariables false in
/--
Weighted `r`-generalized Fibonacci Binet asymptotics with ratio limit: there is
`C > 0` with `a n = C * lam ^ n + o(lam ^ n)`, and `a (n+1) / a n → lam`.
Zero-based `a : ℕ → ℝ` corresponds to one-based `a_{n+1}`; `c`, `A : Fin r → ℝ`
correspond to `c_{k+1}`, `A_{k+1}`; `ha_init` and `ha_rec` encode
`a_n = c_n` for `n = 1, ..., r` and `a_n = ∑ A_k a_{n-k}` for `n > r`. The
dominant-root assumptions (`hlam_pos`, `hlam_root`, `hlam_simple`, `hlam_dom`)
encode the source's "dominant root, a simple positive root of the
characteristic polynomial."

Source: Passawan Noppakaew and Thanakorn Prinyasart, "Complete Sequences of
Weighted r-Generalized Fibonacci Powers," Journal of Integer Sequences 24
(2021), Article 21.5.4, Proposition (label `binet`), lines 119–126,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Prinyasart/prin3.tex
Proves `Wanted` entry `binet`.
It follows from `binet_general`; the hypotheses `hlam_simple` and `hlam_dom` are unused and
keep the source's shape.
-/
theorem binet
    (r : ℕ) (hr : 2 ≤ r)
    (A c : Fin r → ℝ)
    (hA : ∀ k, 0 ≤ A k)
    (hc : ∀ k, 0 ≤ c k)
    (hAr : ∃ i : Fin r, i.val + 1 = r ∧ 0 < A i)
    (hcpos : ∃ k₀, 0 < c k₀)
    (hgcd : ∀ d : ℕ, (∀ k : Fin r, 0 < A k → d ∣ k.val + 1) → d = 1)
    (a : ℕ → ℝ)
    (ha_init : ∀ n (h : n < r), a n = c ⟨n, h⟩)
    (ha_rec : ∀ n, r ≤ n → a n = Finset.sum Finset.univ (fun k : Fin r => A k * a (n - 1 - k.val)))
    (p : Polynomial ℝ)
    (hp : p = Polynomial.X ^ r -
      Finset.sum Finset.univ (fun k : Fin r =>
        Polynomial.C (A k) * Polynomial.X ^ (r - 1 - k.val)))
    (lam : ℝ)
    (hlam_pos : 0 < lam)
    (hlam_root : p.IsRoot lam)
    (hlam_simple : ¬ p.derivative.IsRoot lam)
    (hlam_dom : ∀ z : ℂ, (p.map Complex.ofRealHom).IsRoot z → ‖z‖ ≤ lam ∧ (‖z‖ = lam → z = ↑lam)) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsLittleO Filter.atTop (fun n => a n - C * lam ^ n)
        (fun n => lam ^ n) ∧
      Filter.Tendsto (fun n => a (n + 1) / a n) Filter.atTop (nhds lam) :=
  binet_general r hr A c hA hc hAr hcpos hgcd a ha_init ha_rec p hp lam hlam_pos hlam_root

end MetaMathlibExt
