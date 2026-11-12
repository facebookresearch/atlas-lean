/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStoppedWalk










namespace StatMech.Universality

open Finset

noncomputable section


noncomputable def isingLeapfrogKilledKernel (R t : Nat)
    (p q : IsingLeapfrogBox R) : Real :=
  if isingLeapfrogBoxBoundary R q then 0
  else isingLeapfrogStoppedKernel R t p q


noncomputable def isingLeapfrogExitKernel (R t : Nat)
    (p q : IsingLeapfrogBox R) : Real :=
  if isingLeapfrogBoxBoundary R q then
    isingLeapfrogStoppedKernel R t p q
  else 0

theorem isingLeapfrogStoppedKernel_eq_killed_add_exit (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t p q =
      isingLeapfrogKilledKernel R t p q +
        isingLeapfrogExitKernel R t p q := by
  by_cases hq : isingLeapfrogBoxBoundary R q <;>
    simp [isingLeapfrogKilledKernel, isingLeapfrogExitKernel, hq]

theorem isingLeapfrogKilledKernel_nonneg (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogKilledKernel R t p q := by
  unfold isingLeapfrogKilledKernel
  split_ifs
  · exact le_rfl
  · exact isingLeapfrogStoppedKernel_nonneg R t p q

theorem isingLeapfrogExitKernel_nonneg (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogExitKernel R t p q := by
  unfold isingLeapfrogExitKernel
  split_ifs
  · exact isingLeapfrogStoppedKernel_nonneg R t p q
  · exact le_rfl

theorem isingLeapfrogExitKernel_le_one (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogExitKernel R t p q ≤ 1 := by
  unfold isingLeapfrogExitKernel
  split_ifs
  · exact isingLeapfrogStoppedKernel_le_one R t p q
  · norm_num

theorem isingLeapfrogExitKernel_mono (R : Nat)
    (p q : IsingLeapfrogBox R) :
    Monotone (fun t ↦ isingLeapfrogExitKernel R t p q) := by
  apply monotone_nat_of_le_succ
  intro t
  by_cases hq : isingLeapfrogBoxBoundary R q
  · unfold isingLeapfrogExitKernel
    simp only [if_pos hq]
    exact isingLeapfrogStoppedKernel_boundary_mono R t p q hq
  · simp [isingLeapfrogExitKernel, hq]


noncomputable def isingLeapfrogExitKernelLimit (R : Nat)
    (p q : IsingLeapfrogBox R) : Real :=
  ⨆ t, isingLeapfrogExitKernel R t p q

theorem isingLeapfrogExitKernel_tendsto_limit (R : Nat)
    (p q : IsingLeapfrogBox R) :
    Filter.Tendsto (fun t ↦ isingLeapfrogExitKernel R t p q)
      Filter.atTop (nhds (isingLeapfrogExitKernelLimit R p q)) := by
  apply tendsto_atTop_ciSup (isingLeapfrogExitKernel_mono R p q)
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact isingLeapfrogExitKernel_le_one R t p q

theorem isingLeapfrogExitKernel_succ (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogExitKernel R (t + 1) p q =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogExitKernel R t p q
      else
        (isingLeapfrogExitKernel R t (isingLeapfrogSW R p) q +
          isingLeapfrogExitKernel R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogExitKernel R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogExitKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · unfold isingLeapfrogExitKernel
    simp only [if_pos hq]
    exact isingLeapfrogStoppedKernel_succ R t p q
  · simp [isingLeapfrogExitKernel, hq]


theorem isingLeapfrogExitKernel_succ_sub (R t : Nat)
    (p q : IsingLeapfrogBox R) (hq : isingLeapfrogBoxBoundary R q) :
    isingLeapfrogExitKernel R (t + 1) p q -
        isingLeapfrogExitKernel R t p q =
      ∑ r, isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q := by
  classical
  have hadd := isingLeapfrogStoppedKernel_add R t 1 p q
  have hexit : (∑ r, isingLeapfrogExitKernel R t p r *
      isingLeapfrogStoppedKernel R 1 r q) =
      isingLeapfrogExitKernel R t p q := by
    calc
      _ = ∑ r, if r = q then isingLeapfrogExitKernel R t p r else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hbr : isingLeapfrogBoxBoundary R r
        · rw [isingLeapfrogStoppedKernel_of_boundary R 1 r q hbr]
          simp [hbr]
        · have hrq : r ≠ q := fun hrq ↦ hbr (hrq ▸ hq)
          simp [isingLeapfrogExitKernel, hbr, hrq]
      _ = _ := by simp
  have hsplit : (∑ r, isingLeapfrogStoppedKernel R t p r *
      isingLeapfrogStoppedKernel R 1 r q) =
      (∑ r, isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q) +
      ∑ r, isingLeapfrogExitKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← add_mul,
      ← isingLeapfrogStoppedKernel_eq_killed_add_exit R t p r]
  rw [hsplit, hexit] at hadd
  have hexit_eq : isingLeapfrogExitKernel R t p q =
      isingLeapfrogStoppedKernel R t p q := by
    simp [isingLeapfrogExitKernel, hq]
  rw [hexit_eq] at hadd
  unfold isingLeapfrogExitKernel
  simp only [if_pos hq] at hadd ⊢
  linarith


theorem isingLeapfrogExitKernel_eq_sum_flux (R t : Nat)
    (p q : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p)
    (hq : isingLeapfrogBoxBoundary R q) :
    isingLeapfrogExitKernel R t p q =
      ∑ s ∈ range t, ∑ r, isingLeapfrogKilledKernel R s p r *
        isingLeapfrogStoppedKernel R 1 r q := by
  induction t with
  | zero =>
      have hpq : p ≠ q := fun hpq ↦ hp (hpq ▸ hq)
      simp [isingLeapfrogExitKernel, isingLeapfrogStoppedKernel, hq, hpq]
  | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hflux := isingLeapfrogExitKernel_succ_sub R t p q hq
      linarith




theorem isingLeapfrogExitKernelLimit_meanValue (R : Nat)
    (p q : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogExitKernelLimit R (isingLeapfrogSW R p) q +
        isingLeapfrogExitKernelLimit R (isingLeapfrogSE R p hp) q +
        isingLeapfrogExitKernelLimit R (isingLeapfrogNW R p hp) q +
        isingLeapfrogExitKernelLimit R (isingLeapfrogNE R p hp) q =
      4 * isingLeapfrogExitKernelLimit R p q := by
  have hP := (isingLeapfrogExitKernel_tendsto_limit R p q).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hSW := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogSW R p) q
  have hSE := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogSE R p hp) q
  have hNW := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogNW R p hp) q
  have hNE := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogNE R p hp) q
  have hAvg := (((hSW.add hSE).add hNW).add hNE).div_const 4
  have hrec : (fun t ↦ isingLeapfrogExitKernel R (t + 1) p q) =
      fun t ↦ (isingLeapfrogExitKernel R t (isingLeapfrogSW R p) q +
        isingLeapfrogExitKernel R t (isingLeapfrogSE R p hp) q +
        isingLeapfrogExitKernel R t (isingLeapfrogNW R p hp) q +
        isingLeapfrogExitKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
    funext t
    rw [isingLeapfrogExitKernel_succ]
    simp only [dif_neg hp]
  change Filter.Tendsto (fun t ↦
    isingLeapfrogExitKernel R (t + 1) p q) Filter.atTop _ at hP
  rw [hrec] at hP
  have hlim := tendsto_nhds_unique hP hAvg
  linarith

theorem isingLeapfrogExitKernel_sum_eq_boundaryMass (R t : Nat)
    (p : IsingLeapfrogBox R) :
    ∑ q, isingLeapfrogExitKernel R t p q =
      isingLeapfrogStoppedBoundaryMass R t p := by
  classical
  unfold isingLeapfrogExitKernel isingLeapfrogStoppedBoundaryMass
  rw [Finset.sum_filter]

theorem isingLeapfrogKilledKernel_sum_add_boundaryMass_eq_one
    (R t : Nat) (p : IsingLeapfrogBox R) :
    (∑ q, isingLeapfrogKilledKernel R t p q) +
        isingLeapfrogStoppedBoundaryMass R t p = 1 := by
  classical
  rw [← isingLeapfrogExitKernel_sum_eq_boundaryMass]
  rw [← Finset.sum_add_distrib]
  simp_rw [← isingLeapfrogStoppedKernel_eq_killed_add_exit]
  exact isingLeapfrogStoppedKernel_sum_eq_one R t p


noncomputable def isingLeapfrogKilledKernelTimeGradientSq
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogKilledKernel R t p q -
    isingLeapfrogKilledKernel R t' p' q) ^ 2


noncomputable def isingLeapfrogExitKernelTimeGradientSq
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogExitKernel R t p q -
    isingLeapfrogExitKernel R t' p' q) ^ 2

theorem isingLeapfrogExitKernelTimeGradientSq_eq_sum_boundary
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogExitKernelTimeGradientSq R t t' p p' =
      ∑ q with isingLeapfrogBoxBoundary R q,
        (isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q) ^ 2 := by
  classical
  unfold isingLeapfrogExitKernelTimeGradientSq isingLeapfrogExitKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hb : isingLeapfrogBoxBoundary R q <;> simp [hb]

theorem isingLeapfrogStoppedKernelTimeGradientSq_le_killed_add_exit
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤
      2 * (isingLeapfrogKilledKernelTimeGradientSq R t t' p p' +
        isingLeapfrogExitKernelTimeGradientSq R t t' p p') := by
  classical
  unfold isingLeapfrogStoppedKernelTimeGradientSq
    isingLeapfrogKilledKernelTimeGradientSq
    isingLeapfrogExitKernelTimeGradientSq
  calc
    _ ≤ ∑ q, 2 *
        ((isingLeapfrogKilledKernel R t p q -
            isingLeapfrogKilledKernel R t' p' q) ^ 2 +
          (isingLeapfrogExitKernel R t p q -
            isingLeapfrogExitKernel R t' p' q) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [isingLeapfrogStoppedKernel_eq_killed_add_exit R t p q,
        isingLeapfrogStoppedKernel_eq_killed_add_exit R t' p' q]
      nlinarith [sq_nonneg
        ((isingLeapfrogKilledKernel R t p q -
            isingLeapfrogKilledKernel R t' p' q) -
          (isingLeapfrogExitKernel R t p q -
            isingLeapfrogExitKernel R t' p' q))]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]



abbrev IsingLeapfrogPlane := Int × Int

private def isingLeapfrogPlaneSW (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 - 1, p.2 - 1)

private def isingLeapfrogPlaneSE (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 + 1, p.2 - 1)

private def isingLeapfrogPlaneNW (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 - 1, p.2 + 1)

private def isingLeapfrogPlaneNE (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 + 1, p.2 + 1)


noncomputable def isingLeapfrogFreeKernel :
    Nat → IsingLeapfrogPlane → IsingLeapfrogPlane → Real
  | 0, p, q => if p = q then 1 else 0
  | t + 1, p, q =>
      (isingLeapfrogFreeKernel t (isingLeapfrogPlaneSW p) q +
        isingLeapfrogFreeKernel t (isingLeapfrogPlaneSE p) q +
        isingLeapfrogFreeKernel t (isingLeapfrogPlaneNW p) q +
        isingLeapfrogFreeKernel t (isingLeapfrogPlaneNE p) q) / 4

theorem isingLeapfrogFreeKernel_nonneg (t : Nat)
    (p q : IsingLeapfrogPlane) :
    0 ≤ isingLeapfrogFreeKernel t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogFreeKernel
      split_ifs <;> norm_num
  | succ t ih =>
      simp only [isingLeapfrogFreeKernel]
      have hSW := ih (isingLeapfrogPlaneSW p)
      have hSE := ih (isingLeapfrogPlaneSE p)
      have hNW := ih (isingLeapfrogPlaneNW p)
      have hNE := ih (isingLeapfrogPlaneNE p)
      positivity

private theorem isingBinomialWeight_succ (t k : Nat) :
    isingBinomialWeight (t + 1) k =
      (isingBinomialWeight t k + isingBinomialWeightPrev t k) / 2 := by
  cases k with
  | zero =>
      simp [isingBinomialWeight, isingBinomialWeightPrev, pow_succ]
      ring
  | succ k =>
      unfold isingBinomialWeight isingBinomialWeightPrev
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      rw [Nat.choose_succ_succ']
      push_cast
      simp only [isingBinomialWeight]
      rw [pow_succ]
      ring


noncomputable def isingLineBinomialKernel (t : Nat) (x y : Int) : Real :=
  ∑ k ∈ range (t + 1),
    if y = x + 2 * (k : Int) - (t : Int) then
      isingBinomialWeight t k
    else 0

theorem isingLineBinomialKernel_succ (t : Nat) (x y : Int) :
    isingLineBinomialKernel (t + 1) x y =
      (isingLineBinomialKernel t (x - 1) y +
        isingLineBinomialKernel t (x + 1) y) / 2 := by
  unfold isingLineBinomialKernel
  rw [show t + 1 + 1 = t + 2 by omega]
  simp_rw [isingBinomialWeight_succ]
  have hsplit (k : Nat) :
      (if y = x + 2 * (k : Int) - (t + 1 : Nat) then
          (isingBinomialWeight t k + isingBinomialWeightPrev t k) / 2
        else 0) =
        ((if y = x + 2 * (k : Int) - (t + 1 : Nat) then
            isingBinomialWeight t k else 0) +
          (if y = x + 2 * (k : Int) - (t + 1 : Nat) then
            isingBinomialWeightPrev t k else 0)) / 2 := by
    split_ifs <;> simp
  simp_rw [hsplit]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [show t + 2 = (t + 1) + 1 by omega,
      Finset.sum_range_succ]
    simp only [isingBinomialWeight, Nat.choose_succ_self, Nat.cast_zero,
      zero_div, ite_self, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have heq :
        (y = x + 2 * (k : Int) - (t + 1 : Nat)) ↔
          (y = x - 1 + 2 * (k : Int) - (t : Int)) := by omega
    simp only [heq]
  · rw [show t + 2 = (t + 1) + 1 by omega,
      Finset.sum_range_succ']
    simp only [isingBinomialWeightPrev, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel, if_true, ite_self, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have heq :
        (y = x + 2 * ((k + 1 : Nat) : Int) - (t + 1 : Nat)) ↔
          (y = x + 1 + 2 * (k : Int) - (t : Int)) := by
      push_cast
      omega
    simp only [heq]

private noncomputable def isingLeapfrogFreeBinomialKernel
    (t : Nat) (p q : IsingLeapfrogPlane) : Real :=
  isingLineBinomialKernel t p.1 q.1 *
    isingLineBinomialKernel t p.2 q.2

private theorem isingLeapfrogFreeKernel_eq_binomial (t : Nat)
    (p q : IsingLeapfrogPlane) :
    isingLeapfrogFreeKernel t p q =
      isingLeapfrogFreeBinomialKernel t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogFreeKernel isingLeapfrogFreeBinomialKernel
        isingLineBinomialKernel isingBinomialWeight
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose_zero_right, Nat.cast_one,
        pow_zero, div_one]
      split_ifs <;> simp_all [Prod.ext_iff]
  | succ t ih =>
      simp only [isingLeapfrogFreeKernel]
      rw [ih, ih, ih, ih]
      unfold isingLeapfrogFreeBinomialKernel isingLeapfrogPlaneSW
        isingLeapfrogPlaneSE isingLeapfrogPlaneNW isingLeapfrogPlaneNE
      rw [isingLineBinomialKernel_succ,
        isingLineBinomialKernel_succ]
      ring

private noncomputable def isingBinomialMiddleWeight (t : Nat) : Real :=
  (t.choose (t / 2) : Real) / 2 ^ t

private theorem isingBinomialWeight_le_middle (t k : Nat) :
    isingBinomialWeight t k ≤ isingBinomialMiddleWeight t := by
  unfold isingBinomialWeight isingBinomialMiddleWeight
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_middle k t) (by positivity)

private theorem isingBinomialMiddleWeight_nonneg (t : Nat) :
    0 ≤ isingBinomialMiddleWeight t := by
  unfold isingBinomialMiddleWeight
  positivity

theorem isingLineBinomialKernel_nonneg (t : Nat) (x y : Int) :
    0 ≤ isingLineBinomialKernel t x y := by
  unfold isingLineBinomialKernel
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · unfold isingBinomialWeight
    positivity
  · exact le_rfl

private theorem isingLineBinomialKernel_le_middle
    (t : Nat) (x y : Int) :
    isingLineBinomialKernel t x y ≤ isingBinomialMiddleWeight t := by
  by_cases h : ∃ k ∈ range (t + 1),
      y = x + 2 * (k : Int) - (t : Int)
  · rcases h with ⟨k, hk, heq⟩
    unfold isingLineBinomialKernel
    rw [Finset.sum_eq_single k]
    · simp [heq]
      exact isingBinomialWeight_le_middle t k
    · intro b hb hbk
      have hbne : ¬y = x + 2 * (b : Int) - (t : Int) := by
        intro hbeq
        have hcast : (b : Int) = k := by omega
        have : b = k := by exact_mod_cast hcast
        exact hbk this
      simp [hbne]
    · exact fun hknot ↦ (hknot hk).elim
  · have hzero : isingLineBinomialKernel t x y = 0 := by
      unfold isingLineBinomialKernel
      apply Finset.sum_eq_zero
      intro k hk
      have hkne : ¬y = x + 2 * (k : Int) - (t : Int) := by
        intro hkeq
        exact h ⟨k, hk, hkeq⟩
      simp [hkne]
    rw [hzero]
    exact isingBinomialMiddleWeight_nonneg t

private theorem ising_odd_choose_le_two_mul_centralBinom (n : Nat) :
    (2 * n + 1).choose n ≤ 2 * Nat.centralBinom n := by
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.centralBinom]
  · have hp := Nat.choose_succ_succ (2 * n) (n - 1)
    have hle := Nat.choose_le_middle (n - 1) (2 * n)
    rw [show (2 * n) / 2 = n by omega,
      ← Nat.centralBinom_eq_two_mul_choose] at hle
    calc
      (2 * n + 1).choose n =
          (2 * n).choose (n - 1) + (2 * n).choose n := by
        have hs : (n - 1).succ = n := by omega
        rw [hs] at hp
        simpa using hp
      _ ≤ Nat.centralBinom n + Nat.centralBinom n :=
        Nat.add_le_add hle (by rfl)
      _ = 2 * Nat.centralBinom n := by omega

private theorem isingBinomialMiddleWeight_sq_le (t : Nat) :
    isingBinomialMiddleWeight t ^ 2 ≤ 2 / (t + 1 : Real) := by
  rcases Nat.even_or_odd t with ⟨n, hn⟩ | ⟨n, hn⟩
  · subst t
    rw [show isingBinomialMiddleWeight (n + n) =
        (Nat.centralBinom n : Real) / 4 ^ n by
      unfold isingBinomialMiddleWeight Nat.centralBinom
      rw [show (n + n) / 2 = n by omega,
        show n + n = 2 * n by omega]
      rw [show (2 : Real) ^ (2 * n) = 4 ^ n by
        rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]]
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hc := isingCentralBinom_sq_mul_le n
    have hp : ((4 : Real) ^ n) ^ 2 = (16 : Real) ^ n := by
      rw [pow_two, ← mul_pow]
      norm_num
    norm_num [Nat.cast_add] at *
    nlinarith [sq_nonneg (Nat.centralBinom n : Real)]
  · subst t
    rw [show isingBinomialMiddleWeight (2 * n + 1) =
        ((2 * n + 1).choose n : Real) / (2 * 4 ^ n) by
      unfold isingBinomialMiddleWeight
      rw [show (2 * n + 1) / 2 = n by omega, pow_succ]
      congr 1
      rw [show (2 : Real) ^ (2 * n) = 4 ^ n by
        rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]
      ring]
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hc := isingCentralBinom_sq_mul_le n
    have hdNat := ising_odd_choose_le_two_mul_centralBinom n
    have hd : ((2 * n + 1).choose n : Real) ≤
        2 * (Nat.centralBinom n : Real) := by
      exact_mod_cast hdNat
    have hd0 : (0 : Real) ≤ ((2 * n + 1).choose n : Real) := by positivity
    have hc0 : (0 : Real) ≤ Nat.centralBinom n := by positivity
    have hd2 : ((2 * n + 1).choose n : Real) ^ 2 ≤
        (2 * (Nat.centralBinom n : Real)) ^ 2 :=
      (sq_le_sq₀ hd0 (mul_nonneg (by norm_num) hc0)).2 hd
    have hcn : (Nat.centralBinom n : Real) ^ 2 * (n + 1) ≤ 16 ^ n := by
      calc
        _ ≤ (Nat.centralBinom n : Real) ^ 2 * (2 * (n : Real) + 1) := by
          have hn0 : (0 : Real) ≤ n := by positivity
          have hnle : (n : Real) + 1 ≤ 2 * (n : Real) + 1 := by nlinarith
          exact mul_le_mul_of_nonneg_left hnle (sq_nonneg _)
        _ ≤ _ := hc
    have hp : ((4 : Real) ^ n) ^ 2 = (16 : Real) ^ n := by
      rw [pow_two, ← mul_pow]
      norm_num
    norm_num [Nat.cast_add, Nat.cast_mul] at *
    nlinarith [mul_le_mul_of_nonneg_right hd2
      (show (0 : Real) ≤ n + 1 by positivity)]

theorem isingLineBinomialKernel_sq_le (t : Nat) (x y : Int) :
    isingLineBinomialKernel t x y ^ 2 ≤ 2 / (t + 1 : Real) := by
  exact le_trans
    ((sq_le_sq₀ (isingLineBinomialKernel_nonneg t x y)
      (isingBinomialMiddleWeight_nonneg t)).2
        (isingLineBinomialKernel_le_middle t x y))
    (isingBinomialMiddleWeight_sq_le t)



theorem isingLeapfrogFreeKernel_le (t : Nat)
    (p q : IsingLeapfrogPlane) :
    isingLeapfrogFreeKernel t p q ≤ 2 / (t + 1 : Real) := by
  rw [isingLeapfrogFreeKernel_eq_binomial]
  unfold isingLeapfrogFreeBinomialKernel
  have hx0 := isingLineBinomialKernel_nonneg t p.1 q.1
  have hy0 := isingLineBinomialKernel_nonneg t p.2 q.2
  have hx := isingLineBinomialKernel_sq_le t p.1 q.1
  have hy := isingLineBinomialKernel_sq_le t p.2 q.2
  have hC : 0 ≤ 2 / (t + 1 : Real) := by positivity
  nlinarith [sq_nonneg
    (isingLineBinomialKernel t p.1 q.1 -
      isingLineBinomialKernel t p.2 q.2)]

private def isingLeapfrogBoxToPlane {R : Nat}
    (p : IsingLeapfrogBox R) : IsingLeapfrogPlane :=
  ((p.1.1 : Int), (p.2.1 : Int))

private theorem isingLeapfrogBoxToPlane_injective {R : Nat} :
    Function.Injective (@isingLeapfrogBoxToPlane R) := by
  intro p q hpq
  unfold isingLeapfrogBoxToPlane at hpq
  have hx : (p.1.1 : Int) = q.1.1 := by
    simpa using congrArg Prod.fst hpq
  have hy : (p.2.1 : Int) = q.2.1 := by
    simpa using congrArg Prod.snd hpq
  apply Prod.ext <;> apply Fin.ext
  · exact_mod_cast hx
  · exact_mod_cast hy

private theorem isingLeapfrogBoxToPlane_SW {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogSW R p) =
      isingLeapfrogPlaneSW (isingLeapfrogBoxToPlane p) := by
  have hx : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hy : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  unfold isingLeapfrogBoxToPlane isingLeapfrogSW isingLeapfrogWest
    isingLeapfrogSouth isingLeapfrogPlaneSW
  apply Prod.ext <;> simp <;> omega

private theorem isingLeapfrogBoxToPlane_SE {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogSE R p hp) =
      isingLeapfrogPlaneSE (isingLeapfrogBoxToPlane p) := by
  have hy : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  unfold isingLeapfrogBoxToPlane isingLeapfrogSE isingLeapfrogEast
    isingLeapfrogSouth isingLeapfrogPlaneSE
  apply Prod.ext <;> simp <;> omega

private theorem isingLeapfrogBoxToPlane_NW {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogNW R p hp) =
      isingLeapfrogPlaneNW (isingLeapfrogBoxToPlane p) := by
  have hx : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  unfold isingLeapfrogBoxToPlane isingLeapfrogNW isingLeapfrogWest
    isingLeapfrogNorth isingLeapfrogPlaneNW
  apply Prod.ext <;> simp <;> omega

private theorem isingLeapfrogBoxToPlane_NE {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogNE R p hp) =
      isingLeapfrogPlaneNE (isingLeapfrogBoxToPlane p) := by
  unfold isingLeapfrogBoxToPlane isingLeapfrogNE isingLeapfrogEast
    isingLeapfrogNorth isingLeapfrogPlaneNE
  apply Prod.ext <;> simp


theorem isingLeapfrogKilledKernel_le_free (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q ≤
      isingLeapfrogFreeKernel t (isingLeapfrogBoxToPlane p)
        (isingLeapfrogBoxToPlane q) := by
  induction t generalizing p with
  | zero =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · rw [isingLeapfrogKilledKernel]
        simp only [if_pos hq]
        exact isingLeapfrogFreeKernel_nonneg 0 _ _
      · unfold isingLeapfrogKilledKernel
        rw [if_neg hq]
        unfold isingLeapfrogStoppedKernel isingLeapfrogFreeKernel
        by_cases hpq : p = q
        · simp [hpq]
        · simp [hpq, isingLeapfrogBoxToPlane_injective.ne hpq]
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · simp [isingLeapfrogKilledKernel, hq,
          isingLeapfrogFreeKernel_nonneg]
      · by_cases hp : isingLeapfrogBoxBoundary R p
        · rw [isingLeapfrogKilledKernel]
          simp only [if_neg hq]
          rw [isingLeapfrogStoppedKernel_of_boundary R (t + 1) p q hp]
          have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
          simp [hpq, isingLeapfrogFreeKernel_nonneg]
        · rw [isingLeapfrogKilledKernel]
          simp only [if_neg hq, isingLeapfrogStoppedKernel, dif_neg hp,
            isingLeapfrogFreeKernel]
          have hSW := ih (isingLeapfrogSW R p)
          have hSE := ih (isingLeapfrogSE R p hp)
          have hNW := ih (isingLeapfrogNW R p hp)
          have hNE := ih (isingLeapfrogNE R p hp)
          simp only [isingLeapfrogKilledKernel, if_neg hq] at hSW hSE hNW hNE
          rw [isingLeapfrogBoxToPlane_SW p hp] at hSW
          rw [isingLeapfrogBoxToPlane_SE p hp] at hSE
          rw [isingLeapfrogBoxToPlane_NW p hp] at hNW
          rw [isingLeapfrogBoxToPlane_NE p hp] at hNE
          linarith


theorem isingLeapfrogKilledKernel_le (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q ≤ 2 / (t + 1 : Real) := by
  exact le_trans (isingLeapfrogKilledKernel_le_free R t p q)
    (isingLeapfrogFreeKernel_le t _ _)



theorem isingLeapfrogKilledKernel_diffusive_abs_sub_le
    (R ρ : Nat) (p p' q : IsingLeapfrogBox R) (hρ : 0 < ρ) :
    |isingLeapfrogKilledKernel R (ρ * ρ) p q -
        isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q| ≤
      4 / (ρ : Real) ^ 2 := by
  have ha := isingLeapfrogKilledKernel_le R (ρ * ρ) p q
  have hb := isingLeapfrogKilledKernel_le R (ρ * ρ + 1) p' q
  norm_num [Nat.cast_add, Nat.cast_mul] at ha hb
  have hρsq : 0 < (ρ : Real) ^ 2 := by positivity
  have ha' : isingLeapfrogKilledKernel R (ρ * ρ) p q ≤
      2 / (ρ : Real) ^ 2 := by
    refine le_trans ha (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  have hb' : isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q ≤
      2 / (ρ : Real) ^ 2 := by
    refine le_trans hb (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  have ha0 := isingLeapfrogKilledKernel_nonneg R (ρ * ρ) p q
  have hb0 := isingLeapfrogKilledKernel_nonneg R (ρ * ρ + 1) p' q
  have h24 : 2 / (ρ : Real) ^ 2 ≤ 4 / (ρ : Real) ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) hρsq.le
  rw [abs_sub_le_iff]
  constructor <;> linarith






def IsingLeapfrogDiffusiveExitInputs (A B : Real) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    ∀ (R ρ : Nat) (p p' : IsingLeapfrogBox R),
      0 < ρ →
      IsingLeapfrogInteriorMargin R ρ p →
      IsingLeapfrogInteriorMargin R ρ p' →
      IsingLeapfrogDiagonalAdjacent p p' →
      (∀ q, |isingLeapfrogExitKernel R (ρ * ρ) p q -
          isingLeapfrogExitKernel R (ρ * ρ + 1) p' q| ≤
        A / (ρ : Real) ^ 2) ∧
      (∑ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
          isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q|) ≤
        B / (ρ : Real)

theorem IsingLeapfrogDiffusiveExitInputs.kernelInputs
    {A B : Real} (hAB : IsingLeapfrogDiffusiveExitInputs A B) :
    IsingLeapfrogDiffusiveKernelInputs (A + 4) B := by
  refine ⟨add_nonneg hAB.1 (by norm_num), hAB.2.1, ?_⟩
  intro R ρ p p' hρ hp hp' hpp'
  have hinputs := hAB.2.2 R ρ p p' hρ hp hp' hpp'
  refine ⟨?_, hinputs.2⟩
  intro q
  rw [isingLeapfrogStoppedKernel_eq_killed_add_exit R (ρ * ρ) p q,
    isingLeapfrogStoppedKernel_eq_killed_add_exit
      R (ρ * ρ + 1) p' q]
  calc
    |(isingLeapfrogKilledKernel R (ρ * ρ) p q +
          isingLeapfrogExitKernel R (ρ * ρ) p q) -
        (isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q +
          isingLeapfrogExitKernel R (ρ * ρ + 1) p' q)| =
        |(isingLeapfrogKilledKernel R (ρ * ρ) p q -
            isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q) +
          (isingLeapfrogExitKernel R (ρ * ρ) p q -
            isingLeapfrogExitKernel R (ρ * ρ + 1) p' q)| := by
      congr 1
      ring
    _ ≤ |isingLeapfrogKilledKernel R (ρ * ρ) p q -
          isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q| +
        |isingLeapfrogExitKernel R (ρ * ρ) p q -
          isingLeapfrogExitKernel R (ρ * ρ + 1) p' q| :=
      abs_add_le _ _
    _ ≤ 4 / (ρ : Real) ^ 2 + A / (ρ : Real) ^ 2 :=
      add_le_add
        (isingLeapfrogKilledKernel_diffusive_abs_sub_le R ρ p p' q hρ)
        (hinputs.1 q)
    _ = (A + 4) / (ρ : Real) ^ 2 := by ring

theorem IsingLeapfrogDiffusiveExitInputs.gradientBound
    {A B : Real} (hAB : IsingLeapfrogDiffusiveExitInputs A B) :
    IsingLeapfrogDiffusiveGradientBound ((A + 4) * B) :=
  hAB.kernelInputs.gradientBound

end

end StatMech.Universality
