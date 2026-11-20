/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalEnergy
import Code.Universality.IsingFermionicPhysicalRadialPatch
import Mathlib.Data.Nat.Choose.Vandermonde











namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

open Finset



def IsingCellCRAt (F : Nat → Nat → Complex) (i j : Nat) : Prop :=
  F i (j + 1) - F (i + 1) j =
    Complex.I * (F (i + 1) (j + 1) - F i j)



theorem isingCellCRAt_leapfrog_harmonic
    (F : Nat → Nat → Complex) (i j : Nat)
    (hSW : IsingCellCRAt F i j)
    (hSE : IsingCellCRAt F (i + 1) j)
    (hNW : IsingCellCRAt F i (j + 1))
    (hNE : IsingCellCRAt F (i + 1) (j + 1)) :
    F i j + F i (j + 2) + F (i + 2) j + F (i + 2) (j + 2) =
      4 * F (i + 1) (j + 1) := by
  unfold IsingCellCRAt at hSW hSE hNW hNE
  have hI : Complex.I ^ 2 + 1 = 0 := by norm_num
  linear_combination
    -Complex.I * hSW - hSE + hNW + Complex.I * hNE +
      (F i j + F (i + 2) (j + 2) - 2 * F (i + 1) (j + 1)) * hI



noncomputable def fkIsingSquareRadialPatchFullObservableExtension
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) : Nat → Nat → Complex :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

@[simp] theorem fkIsingSquareRadialPatchFullObservableExtension_apply
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchFullObservableExtension n m hn hm i j =
      fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [fkIsingSquareRadialPatchFullObservableExtension, hi, hj]



theorem fkIsingSquareRadialPatchFullObservable_cellCR
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 2 < m) (hj : j + 2 < m) :
    IsingCellCRAt
      (fkIsingSquareRadialPatchFullObservableExtension n m hn hm) i j := by
  by_cases heven : Even (i + 1 + (j + 1))
  · have hquad := fkIsingSquareRadialPatchFullObservable_quad
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt fkIsingSquareRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    simpa using hquad.2.2
  · have hquad := fkIsingSquareRadialPatchFullObservable_quad_of_odd
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt fkIsingSquareRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    have h := hquad.2.2
    simp only [Nat.add_sub_cancel] at h
    linear_combination -h



theorem fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 3 < m) (hj : j + 3 < m) :
    fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j + 2, by omega⟩ +
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ =
      4 * fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
  have hSW := fkIsingSquareRadialPatchFullObservable_cellCR
      n m i j hn hm (by omega) (by omega)
  have hSE := fkIsingSquareRadialPatchFullObservable_cellCR
      n m (i + 1) j hn hm (by omega) (by omega)
  have hNW := fkIsingSquareRadialPatchFullObservable_cellCR
      n m i (j + 1) hn hm (by omega) (by omega)
  have hNE := fkIsingSquareRadialPatchFullObservable_cellCR
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
  have h := isingCellCRAt_leapfrog_harmonic
    (fkIsingSquareRadialPatchFullObservableExtension n m hn hm) i j
    hSW hSE hNW hNE
  simpa [fkIsingSquareRadialPatchFullObservableExtension,
    show i < m by omega, show j < m by omega,
    show i + 1 < m by omega, show j + 1 < m by omega,
    show i + 2 < m by omega, show j + 2 < m by omega] using h





theorem isingCentralBinom_sq_mul_le (n : Nat) :
    ((Nat.centralBinom n : Real) ^ 2) * (2 * n + 1) ≤ (16 : Real) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hrecNat := Nat.succ_mul_centralBinom_succ n
      have hrec := congrArg (fun k : Nat ↦ (k : Real)) hrecNat
      push_cast at hrec
      rw [pow_succ]
      have hfac : 0 ≤ 4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left ih hfac
      have hpoly :
          4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1) ≤
            16 * ((n : Real) + 1) ^ 2 := by nlinarith
      have hpow : 0 ≤ (16 : Real) ^ n := by positivity
      have hrecSq := congrArg (fun x : Real ↦ x ^ 2) hrec
      change (((n : Real) + 1) *
          (Nat.centralBinom (n + 1) : Real)) ^ 2 =
        (2 * (2 * (n : Real) + 1) * Nat.centralBinom n) ^ 2 at hrecSq
      have hmain :
          ((n : Real) + 1) ^ 2 *
              (((Nat.centralBinom (n + 1) : Real) ^ 2) *
                (2 * (n + 1 : Nat) + 1)) ≤
            ((n : Real) + 1) ^ 2 * (16 * (16 : Real) ^ n) := by
        calc
          _ = (((n : Real) + 1) *
                (Nat.centralBinom (n + 1) : Real)) ^ 2 *
                (2 * (n : Real) + 3) := by
              push_cast
              ring
          _ = (2 * (2 * (n : Real) + 1) *
                Nat.centralBinom n) ^ 2 * (2 * (n : Real) + 3) := by
              rw [hrecSq]
          _ = (4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1)) *
                (((Nat.centralBinom n : Real) ^ 2) *
                  (2 * (n : Real) + 1)) := by ring
          _ ≤ (4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1)) *
                (16 : Real) ^ n := hmul
          _ ≤ (16 * ((n : Real) + 1) ^ 2) * (16 : Real) ^ n :=
            mul_le_mul_of_nonneg_right hpoly hpow
          _ = _ := by ring
      have hmain' := (by
        simpa only [Nat.cast_add, Nat.cast_one] using hmain)
      have hcancel := le_of_mul_le_mul_left hmain'
        (show 0 < ((n : Real) + 1) ^ 2 by positivity)
      convert hcancel using 1 <;> push_cast <;> ring


noncomputable def isingBinomialWeight (n k : Nat) : Real :=
  (n.choose k : Real) / 2 ^ n


noncomputable def isingBinomialWeightPrev (n k : Nat) : Real :=
  if k = 0 then 0 else isingBinomialWeight n (k - 1)

theorem isingBinomialWeight_sq_sum (n : Nat) :
    ∑ k ∈ range (n + 1), isingBinomialWeight n k ^ 2 =
      (Nat.centralBinom n : Real) / 4 ^ n := by
  have h := Nat.sum_range_choose_sq n
  have hR : (∑ k ∈ range (n + 1), (n.choose k : Real) ^ 2) =
      (Nat.centralBinom n : Real) := by
    exact_mod_cast h
  unfold isingBinomialWeight
  simp_rw [div_pow, ← Finset.sum_div]
  rw [hR]
  congr 1
  rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
    Nat.mul_comm n 2]

private theorem ising_sum_choose_adjacent (n : Nat) :
    ∑ k ∈ range (n + 2),
        n.choose k * (if k = 0 then 0 else n.choose (k - 1)) =
      (2 * n).choose (n + 1) := by
  rw [two_mul, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n + 2 := Finset.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k
    simp
  · rw [if_neg hk0]
    congr 1
    symm
    rw [← Nat.choose_symm (by omega : n + 1 - k ≤ n)]
    congr 1
    omega


theorem isingBinomialWeight_diff_sq_sum (n : Nat) :
    ∑ k ∈ range (n + 2),
        (isingBinomialWeight n k - isingBinomialWeightPrev n k) ^ 2 =
      2 * (Nat.centralBinom n : Real) / ((n + 1) * 4 ^ n) := by
  have hA : (∑ k ∈ range (n + 2), isingBinomialWeight n k ^ 2) =
      (Nat.centralBinom n : Real) / 4 ^ n := by
    rw [Finset.sum_range_succ, isingBinomialWeight_sq_sum]
    simp [isingBinomialWeight]
  have hB : (∑ k ∈ range (n + 2), isingBinomialWeightPrev n k ^ 2) =
      (Nat.centralBinom n : Real) / 4 ^ n := by
    rw [Finset.sum_range_succ']
    simpa [isingBinomialWeightPrev] using isingBinomialWeight_sq_sum n
  have hCrossNat := ising_sum_choose_adjacent n
  have hCrossCast :
      (∑ k ∈ range (n + 2),
        (n.choose k : Real) *
          (if k = 0 then 0 else (n.choose (k - 1) : Real))) =
        ((2 * n).choose (n + 1) : Real) := by
    exact_mod_cast hCrossNat
  have hCross : (∑ k ∈ range (n + 2),
      isingBinomialWeight n k * isingBinomialWeightPrev n k) =
      ((2 * n).choose (n + 1) : Real) / 4 ^ n := by
    calc
      _ = ∑ k ∈ range (n + 2),
          ((n.choose k : Real) *
            (if k = 0 then 0 else (n.choose (k - 1) : Real))) / 4 ^ n := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hk0 : k = 0
            · subst k
              simp [isingBinomialWeight, isingBinomialWeightPrev]
            simp only [isingBinomialWeightPrev, hk0, if_false,
              isingBinomialWeight]
            rw [div_mul_div_comm]
            congr 1
            rw [show (4 : Real) ^ n = 2 ^ (2 * n) by
              rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]
            rw [← pow_add]
            congr 1
            omega
      _ = (∑ k ∈ range (n + 2),
          (n.choose k : Real) *
            (if k = 0 then 0 else (n.choose (k - 1) : Real))) / 4 ^ n := by
            rw [Finset.sum_div]
      _ = _ := by rw [hCrossCast]
  have hchooseNat := Nat.choose_succ_right_eq (n := 2 * n) (k := n)
  rw [show 2 * n - n = n by omega] at hchooseNat
  have hchoose :
      ((n + 1 : Nat) : Real) * ((2 * n).choose (n + 1) : Real) =
        (n : Real) * (Nat.centralBinom n : Real) := by
    have hchooseRaw :
        (((n + 1) * (2 * n).choose (n + 1) : Nat) : Real) =
          ((n * (2 * n).choose n : Nat) : Real) := by
      exact_mod_cast (by simpa [mul_comm] using hchooseNat)
    simpa [Nat.centralBinom, mul_comm] using hchooseRaw
  have hchoose' :
      ((n : Real) + 1) * ((2 * n).choose (n + 1) : Real) =
        (n : Real) * (Nat.centralBinom n : Real) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hchoose
  have hdiff :
      ((Nat.centralBinom n : Real) - ((2 * n).choose (n + 1) : Real)) *
          (n + 1) = (Nat.centralBinom n : Real) := by
    calc
      _ = (Nat.centralBinom n : Real) * (n + 1) -
          (n + 1) * ((2 * n).choose (n + 1) : Real) := by ring
      _ = (Nat.centralBinom n : Real) * (n + 1) -
          (n : Real) * Nat.centralBinom n := by rw [hchoose']
      _ = _ := by ring
  calc
    _ = ∑ k ∈ range (n + 2),
        (isingBinomialWeight n k ^ 2 + isingBinomialWeightPrev n k ^ 2 -
          2 * (isingBinomialWeight n k * isingBinomialWeightPrev n k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (∑ k ∈ range (n + 2), isingBinomialWeight n k ^ 2) +
          (∑ k ∈ range (n + 2), isingBinomialWeightPrev n k ^ 2) -
          2 * (∑ k ∈ range (n + 2),
            isingBinomialWeight n k * isingBinomialWeightPrev n k) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.mul_sum]
    _ = 2 * (Nat.centralBinom n : Real) / 4 ^ n -
          2 * (((2 * n).choose (n + 1) : Real) / 4 ^ n) := by
          rw [hA, hB, hCross]
          ring
    _ = _ := by
      have hn : (n + 1 : Real) ≠ 0 := by positivity
      have hp : (4 : Real) ^ n ≠ 0 := by positivity
      field_simp
      nlinarith [hdiff]



theorem isingBinomialKernel_gradient_sq_sum_le (n : Nat) :
    (∑ a ∈ range (n + 2), ∑ b ∈ range (n + 1),
      ((isingBinomialWeight n a - isingBinomialWeightPrev n a) *
        isingBinomialWeight n b) ^ 2) ≤
        2 / ((n + 1 : Real) ^ 2) := by
  have hfactor :
      (∑ a ∈ range (n + 2), ∑ b ∈ range (n + 1),
        ((isingBinomialWeight n a - isingBinomialWeightPrev n a) *
          isingBinomialWeight n b) ^ 2) =
      (∑ a ∈ range (n + 2),
          (isingBinomialWeight n a - isingBinomialWeightPrev n a) ^ 2) *
        (∑ b ∈ range (n + 1), isingBinomialWeight n b ^ 2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hfactor, isingBinomialWeight_diff_sq_sum,
    isingBinomialWeight_sq_sum]
  have hc := isingCentralBinom_sq_mul_le n
  have hpow : (16 : Real) ^ n = 4 ^ (n * 2) := by
    rw [show (16 : Real) = 4 ^ 2 by norm_num, ← pow_mul,
      Nat.mul_comm 2 n]
  calc
    2 * (Nat.centralBinom n : Real) / ((n + 1) * 4 ^ n) *
          ((Nat.centralBinom n : Real) / 4 ^ n) =
        2 * ((Nat.centralBinom n : Real) ^ 2 * (2 * n + 1)) /
          (((n + 1 : Real) * (2 * n + 1)) * (16 : Real) ^ n) := by
            field_simp
            rw [hpow]
            ring
    _ ≤ 2 * (16 : Real) ^ n /
          (((n + 1 : Real) * (2 * n + 1)) * (16 : Real) ^ n) := by
            gcongr
    _ = 2 / ((n + 1 : Real) * (2 * n + 1)) := by field_simp
    _ ≤ 2 / ((n + 1 : Real) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hn : (0 : Real) ≤ n := by positivity
      nlinarith


theorem isingComplex_normSq_sum_mul_le {ι : Type} (s : Finset ι)
    (c : ι → Real) (z : ι → Complex) :
    Complex.normSq (∑ x ∈ s, (c x : Complex) * z x) ≤
      (∑ x ∈ s, c x ^ 2) * (∑ x ∈ s, Complex.normSq (z x)) := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm : ‖∑ x ∈ s, (c x : Complex) * z x‖ ≤
      ∑ x ∈ s, |c x| * ‖z x‖ := by
    calc
      _ ≤ ∑ x ∈ s, ‖(c x : Complex) * z x‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (∑ x ∈ s, |c x| * ‖z x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun x hx ↦
        mul_nonneg (abs_nonneg _) (norm_nonneg _))).mpr hnorm
    _ ≤ (∑ x ∈ s, |c x| ^ 2) * (∑ x ∈ s, ‖z x‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun x ↦ |c x|) (fun x ↦ ‖z x‖)
    _ = _ := by
      simp only [sq_abs, Complex.normSq_eq_norm_sq]



theorem isingBinomialMean_normSq_sub_le
    (F : Nat → Nat → Complex) (t x y : Nat) (E : Real)
    (left right : Complex)
    (hleft : left = ∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1),
      ((isingBinomialWeight t a * isingBinomialWeight t b : Real) : Complex) *
        F (x + 2 * a) (y + 2 * b))
    (hright : right = ∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1),
      ((isingBinomialWeightPrev t a * isingBinomialWeight t b : Real) : Complex) *
        F (x + 2 * a) (y + 2 * b))
    (hL2 : (∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1),
      Complex.normSq (F (x + 2 * a) (y + 2 * b))) ≤ E) :
    Complex.normSq (left - right) ≤ 2 * E / (t + 1 : Real) ^ 2 := by
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  push_cast
  let s := (range (t + 2)).product (range (t + 1))
  let c : Nat × Nat → Real := fun p ↦
    (isingBinomialWeight t p.1 - isingBinomialWeightPrev t p.1) *
      isingBinomialWeight t p.2
  let z : Nat × Nat → Complex := fun p ↦
    F (x + 2 * p.1) (y + 2 * p.2)
  have hcoeff (a b : Nat) :
      (isingBinomialWeight t a : Complex) *
          (isingBinomialWeight t b : Complex) -
        (isingBinomialWeightPrev t a : Complex) *
          (isingBinomialWeight t b : Complex) = (c (a, b) : Complex) := by
    dsimp [c]
    push_cast
    ring
  simp_rw [hcoeff]
  change Complex.normSq (∑ a ∈ range (t + 2),
      ∑ b ∈ range (t + 1), (c (a, b) : Complex) * z (a, b)) ≤ _
  rw [← Finset.sum_product']
  have hcs := isingComplex_normSq_sum_mul_le s c z
  calc
    Complex.normSq (∑ p ∈ s, (c p : Complex) * z p) ≤
        (∑ p ∈ s, c p ^ 2) * (∑ p ∈ s, Complex.normSq (z p)) := hcs
    _ ≤ (2 / (t + 1 : Real) ^ 2) * E := by
      apply mul_le_mul (by
          simpa [s, c, Finset.sum_product] using
            isingBinomialKernel_gradient_sq_sum_le t)
        (by simpa [s, z, Finset.sum_product] using hL2)
        (Finset.sum_nonneg fun p hp ↦ Complex.normSq_nonneg _)
        (by positivity)
    _ = _ := by ring

end

end StatMech.Universality
