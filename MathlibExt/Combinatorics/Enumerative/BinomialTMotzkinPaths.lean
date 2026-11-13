/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
open scoped BigOperators
namespace MetaMathlibExt
private abbrev binomialTMotzkinStep (t : ℕ) := Σ k : Fin (t + 1), Fin (Nat.choose t k)
private abbrev binomialTMotzkinHeight (t : ℕ) : binomialTMotzkinStep t → ℤ :=
  fun s => 1 - (s.1 : ℤ)
private noncomputable def binomialTMotzkinCount (t n : ℕ) (h : ℤ) : ℕ :=
  Fintype.card {p : Fin n → binomialTMotzkinStep t //
    (∀ m : Fin (n + 1),
      0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
    ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h}

private theorem binomialTMotzkinCount_zero (t : ℕ) (h : ℤ) :
    binomialTMotzkinCount t 0 h = if h = 0 then 1 else 0 := by
  unfold binomialTMotzkinCount
  by_cases hh : h = 0
  · subst hh; simp
  · have : IsEmpty {p : Fin 0 → binomialTMotzkinStep t //
        (∀ m : Fin (0 + 1),
          0 ≤ ∑ i : Fin 0, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
        ∑ i : Fin 0, binomialTMotzkinHeight t (p i) = h} :=
      ⟨fun ⟨p, _, htot⟩ => by simp at htot; exact hh htot.symm⟩
    rw [Fintype.card_eq_zero]
    simp [hh]

private theorem binomialTMotzkinCount_of_neg (t n : ℕ) (h : ℤ) (hh : h < 0) :
    binomialTMotzkinCount t n h = 0 := by
  unfold binomialTMotzkinCount
  have : IsEmpty {p : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
        ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h} := by
    constructor
    rintro ⟨p, hpref, htot⟩
    have hlast := hpref (Fin.last n)
    have heq : (∑ i : Fin n, if i.1 < (Fin.last n).1 then binomialTMotzkinHeight t (p i) else 0)
        = ∑ i : Fin n, binomialTMotzkinHeight t (p i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.1 < (Fin.last n).1 := by
        rw [Fin.val_last]; exact i.isLt
      rw [ite_eq_left hi]
    rw [heq, htot] at hlast
    omega
  rw [Fintype.card_eq_zero]

private theorem binomialTMotzkinCount_of_gt (t n : ℕ) (h : ℤ) (hh : (n : ℤ) < h) :
    binomialTMotzkinCount t n h = 0 := by
  unfold binomialTMotzkinCount
  have : IsEmpty {p : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
        ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h} := by
    constructor
    rintro ⟨p, _, htot⟩
    have hle : ∑ i : Fin n, binomialTMotzkinHeight t (p i) ≤ (n : ℤ) := by
      calc ∑ i : Fin n, binomialTMotzkinHeight t (p i)
          ≤ Finset.card (Finset.univ : Finset (Fin n)) • (1 : ℤ) := by
            apply Finset.sum_le_card_nsmul
            intro i _
            change (1 : ℤ) - ((p i).1 : ℤ) ≤ 1
            have hnn : (0 : ℤ) ≤ (((p i).1 : ℤ)) := by positivity
            omega
        _ = (n : ℤ) := by simp
    omega
  rw [Fintype.card_eq_zero]

private theorem snoc_total (t n : ℕ) (q : Fin n → binomialTMotzkinStep t)
    (s : binomialTMotzkinStep t) :
    ∑ i : Fin (n + 1), binomialTMotzkinHeight t
        (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i)
      = (∑ i : Fin n, binomialTMotzkinHeight t (q i)) + binomialTMotzkinHeight t s := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

private theorem snoc_prefix_castSucc (t n : ℕ) (q : Fin n → binomialTMotzkinStep t)
    (s : binomialTMotzkinStep t) (m' : Fin (n + 1)) :
    (∑ i : Fin (n + 1), if i.1 < (Fin.castSucc m').1
      then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) else 0)
      = ∑ i : Fin n, if i.1 < m'.1 then binomialTMotzkinHeight t (q i) else 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last]
  have hle : m'.val ≤ n := Nat.le_of_lt_succ m'.isLt
  rw [ite_eq_right (by omega)]
  simp

private theorem snoc_prefix_last (t n : ℕ) (q : Fin n → binomialTMotzkinStep t)
    (s : binomialTMotzkinStep t) :
    (∑ i : Fin (n + 1), if i.1 < (Fin.last (n + 1)).1
      then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) else 0)
      = ∑ i : Fin (n + 1), binomialTMotzkinHeight t
          (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) := by
  rw [Fin.val_last]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.1 < n + 1 := i.isLt
  rw [ite_eq_left hi]

private theorem snoc_pred_iff (t n : ℕ) (h : ℤ) (hh : 0 ≤ h)
    (q : Fin n → binomialTMotzkinStep t) (s : binomialTMotzkinStep t) :
    ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1
          then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) else
              0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t
          (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) = h)
    ↔ ((∀ m' : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m'.1 then binomialTMotzkinHeight t (q i) else 0)
      ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s) := by
  rw [Fin.forall_fin_succ']
  constructor
  · rintro ⟨⟨hpref, hlast⟩, htot⟩
    rw [snoc_total] at htot
    refine ⟨?_, by omega⟩
    intro m'
    have h2 := hpref m'
    rwa [snoc_prefix_castSucc] at h2
  · rintro ⟨hpref, htot⟩
    have htot' : ∑ i : Fin (n + 1),
        binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) = h := by
      rw [snoc_total]
      omega
    refine ⟨⟨?_, ?_⟩, htot'⟩
    · intro m'
      have h2 := hpref m'
      rwa [snoc_prefix_castSucc]
    · rw [snoc_prefix_last, htot']
      exact hh

private theorem pred_iff_symm (t n : ℕ) (h : ℤ) (hh : 0 ≤ h)
    (p : Fin (n + 1) → binomialTMotzkinStep t) :
    ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h)
    ↔ ((∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1
          then binomialTMotzkinHeight t (((Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
              p).2 i) else 0)
      ∧ ∑ i : Fin n, binomialTMotzkinHeight t
          (((Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm p).2 i)
        = h - binomialTMotzkinHeight t (((Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
            p).1)) := by
  have h1 : ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h)
      ↔ ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1
          then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t)
              (Fin.init p) (p (Fin.last n)) i) else 0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t
          (Fin.snoc (α := fun _ => binomialTMotzkinStep t) (Fin.init p) (p (Fin.last n)) i) =
              h) := by
    rw [Fin.snoc_init_self p]
  have h2 := snoc_pred_iff t n h hh (Fin.init p) (p (Fin.last n))
  exact h1.trans h2

private def baseEquiv (t n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    {p : Fin (n + 1) → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
        ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h}
    ≃ {y : binomialTMotzkinStep t × (Fin n → binomialTMotzkinStep t) //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (y.2 i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (y.2 i) = h - binomialTMotzkinHeight t y.1} :=
  Equiv.subtypeEquiv (Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
    (fun p => pred_iff_symm t n h hh p)

private def repackEquiv (t n : ℕ) (h : ℤ) :
    {y : binomialTMotzkinStep t × (Fin n → binomialTMotzkinStep t) //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (y.2 i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (y.2 i) = h - binomialTMotzkinHeight t y.1}
    ≃ Σ s : binomialTMotzkinStep t, {q : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s} where
  toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem binomialTMotzkinCount_succ (t n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    binomialTMotzkinCount t (n + 1) h
      = ∑ s : binomialTMotzkinStep t, binomialTMotzkinCount t n
          (h - binomialTMotzkinHeight t s) := by
  unfold binomialTMotzkinCount
  calc Fintype.card {p : Fin (n + 1) → binomialTMotzkinStep t //
        (∀ m : Fin (n + 1 + 1),
          0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
        ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h}
      = Fintype.card (Σ s : binomialTMotzkinStep t, {q : Fin n → binomialTMotzkinStep t //
        (∀ m : Fin (n + 1),
          0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
          ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s}) :=
        Fintype.card_congr ((baseEquiv t n h hh).trans (repackEquiv t n h))
    _ = ∑ s : binomialTMotzkinStep t, Fintype.card {q : Fin n → binomialTMotzkinStep t //
        (∀ m : Fin (n + 1),
          0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
          ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s} :=
        Fintype.card_sigma
    _ = ∑ s : binomialTMotzkinStep t, binomialTMotzkinCount t n (h - binomialTMotzkinHeight t s) :=
        Fintype.sum_congr _ _ (fun s => rfl)

private theorem binomialTMotzkinStep_sum (t : ℕ) (f : ℤ → ℕ) :
    ∑ s : binomialTMotzkinStep t, f (binomialTMotzkinHeight t s)
      = ∑ k ∈ Finset.range (t + 1), Nat.choose t k * f (1 - (k : ℤ)) := by
  rw [Fintype.sum_sigma]
  have hconst : ∀ (k : Fin (t + 1)) (c : Fin (Nat.choose t ↑k)),
      f (binomialTMotzkinHeight t ⟨k, c⟩) = f (1 - ((↑k : ℕ) : ℤ)) := by
    intro k c
    congr 1
  have hinner : ∀ k : Fin (t + 1),
      (∑ c : Fin (Nat.choose t ↑k), f (binomialTMotzkinHeight t ⟨k, c⟩))
        = Nat.choose t ↑k * f (1 - ((↑k : ℕ) : ℤ)) := by
    intro k
    trans ∑ _c : Fin (Nat.choose t ↑k), f (1 - ((↑k : ℕ) : ℤ))
    · exact Finset.sum_congr rfl (fun c _ => hconst k c)
    · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  trans ∑ k : Fin (t + 1), Nat.choose t ↑k * f (1 - ((↑k : ℕ) : ℤ))
  · exact Fintype.sum_congr _ _ (fun k => hinner k)
  · exact Fin.sum_univ_eq_sum_range (fun n : ℕ => Nat.choose t n * f (1 - (n : ℤ))) (t + 1)

private noncomputable def binomialTMotzkinDeficitPoly (t N : ℕ) : Polynomial ℚ :=
  (1 + Polynomial.X) ^ (t * N) - Polynomial.C (t : ℚ) * Polynomial.X * (1 + Polynomial.X) ^
      (t * N - 1)

private theorem binomialTMotzkinDeficitPoly_succ (t N : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N) :
    binomialTMotzkinDeficitPoly t (N + 1)
      = (1 + Polynomial.X) ^ t * binomialTMotzkinDeficitPoly t N := by
  unfold binomialTMotzkinDeficitPoly
  have hpos : 1 ≤ t * N := by
    calc 1 = 1 * 1 := by ring
    _ ≤ t * N := Nat.mul_le_mul ht hN
  have h1 : t * (N + 1) = t * N + t := by ring
  have h2 : t * (N + 1) - 1 = t + (t * N - 1) := by omega
  rw [h2, h1, pow_add]
  ring

private theorem binomialTMotzkinDeficitPoly_coeff_zero (t N : ℕ) :
    (binomialTMotzkinDeficitPoly t N).coeff 0 = 1 := by
  unfold binomialTMotzkinDeficitPoly
  rw [Polynomial.coeff_sub]
  have hX : (Polynomial.C (t : ℚ) * Polynomial.X * (1 + Polynomial.X) ^ (t * N - 1)).coeff 0 =
      0 := by
    rw [mul_assoc, Polynomial.coeff_C_mul]
    simp
  rw [hX, sub_zero]
  rw [Polynomial.coeff_one_add_X_pow]
  simp

private theorem binomialTMotzkinDeficitPoly_coeff_succ (t N r : ℕ) :
    (binomialTMotzkinDeficitPoly t N).coeff (r + 1)
      = (Nat.choose (t * N) (r + 1) : ℚ) - (t : ℚ) * (Nat.choose (t * N - 1) r : ℚ) := by
  unfold binomialTMotzkinDeficitPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow]
  congr 1
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_one_add_X_pow]

private theorem powerSeries_coeff_mul_congr_of_coeff_eq {R : Type*} [CommSemiring R]
    (U V W : PowerSeries R) (N : ℕ) (h : ∀ m ≤ N, U.coeff m = V.coeff m) :
    (W * U).coeff N = (W * V).coeff N := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hmem := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hj : p.2 ≤ N := by omega
  rw [h p.2 hj]

private theorem binomialTMotzkin_pow_coeff_shift_a (Q : PowerSeries ℚ) (t n : ℕ) :
    ((1 + PowerSeries.X * Q) ^ t).coeff (n + 1)
      = ∑ k ∈ Finset.range t, (Nat.choose t (k + 1) : ℚ) * (PowerSeries.X ^ k * Q ^ (k + 1)).coeff
          n := by
  have hcomm : (1 + PowerSeries.X * Q : PowerSeries ℚ) = PowerSeries.X * Q + 1 := by ring
  rw [hcomm, add_pow, map_sum, Finset.sum_range_succ']
  have hzero : ((PowerSeries.X * Q) ^ 0 * 1 ^ (t - 0) * Nat.cast (Nat.choose t 0)).coeff (n + 1) =
      0 := by
    simp
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have heq : (PowerSeries.X * Q : PowerSeries ℚ) ^ (k + 1) * 1 ^ (t - (k + 1)) * Nat.cast
      (Nat.choose t (k + 1))
      = Nat.cast (Nat.choose t (k + 1)) * (PowerSeries.X * (PowerSeries.X ^ k * Q ^ (k + 1))) := by
    ring
  rw [heq, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_succ_X_mul]

private theorem binomialTMotzkin_pow_coeff_shift_b (Q : PowerSeries ℚ) (t n h : ℕ) (hh : 1 ≤ h) :
    (PowerSeries.X ^ h * Q ^ h * (1 + PowerSeries.X * Q) ^ t).coeff (n + 1)
      = ∑ k ∈ Finset.range (t + 1), (Nat.choose t k : ℚ) *
          (PowerSeries.X ^ (h - 1 + k) * Q ^ (h + k)).coeff n := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hcomm : (1 + PowerSeries.X * Q : PowerSeries ℚ) = PowerSeries.X * Q + 1 := by ring
  rw [hcomm, add_pow, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have heq : (PowerSeries.X : PowerSeries ℚ) ^ (h' + 1) * Q ^ (h' + 1) *
      ((PowerSeries.X * Q) ^ k * 1 ^ (t - k) * Nat.cast (Nat.choose t k))
      = Nat.cast (Nat.choose t k) * (PowerSeries.X *
          (PowerSeries.X ^ (h' + k) * Q ^ (h' + 1 + k))) := by
    ring
  rw [heq, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_succ_X_mul]

private theorem binomialTMotzkinCount_succ_height (t n h : ℕ) :
    binomialTMotzkinCount t (n + 1) h
      = ∑ k ∈ Finset.range (t + 1),
        Nat.choose t k * binomialTMotzkinCount t n ((h : ℤ) + (k : ℤ) - 1) := by
  calc binomialTMotzkinCount t (n + 1) h
      = ∑ s : binomialTMotzkinStep t,
        binomialTMotzkinCount t n ((h : ℤ) - binomialTMotzkinHeight t s) :=
        binomialTMotzkinCount_succ t n _ (Nat.cast_nonneg _)
    _ = ∑ k ∈ Finset.range (t + 1),
        Nat.choose t k * binomialTMotzkinCount t n ((h : ℤ) - (1 - (k : ℤ))) :=
        binomialTMotzkinStep_sum t (fun x : ℤ => binomialTMotzkinCount t n ((h : ℤ) - x))
    _ = ∑ k ∈ Finset.range (t + 1),
        Nat.choose t k * binomialTMotzkinCount t n ((h : ℤ) + (k : ℤ) - 1) := by
        apply Finset.sum_congr rfl
        intro k _
        have hkk : (h : ℤ) - (1 - (k : ℤ)) = (h : ℤ) + (k : ℤ) - 1 := by ring
        rw [hkk]

private theorem binomialTMotzkinCount_succ_zero (t n : ℕ) :
    binomialTMotzkinCount t (n + 1) 0
      = ∑ k ∈ Finset.range t,
        Nat.choose t (k + 1) * binomialTMotzkinCount t n k := by
  have hLHS : binomialTMotzkinCount t (n + 1) (0 : ℤ)
      = binomialTMotzkinCount t (n + 1) (((0 : ℕ)) : ℤ) := by simp
  have hmain := binomialTMotzkinCount_succ_height t n 0
  rw [hLHS, hmain, Finset.sum_range_succ']
  have hz : binomialTMotzkinCount t n ((((0 : ℕ)) : ℤ) + ((((0 : ℕ))) : ℤ) - 1) = 0 := by
    have hneg : (((((0 : ℕ))) : ℤ) + ((((0 : ℕ))) : ℤ) - 1 : ℤ) = -1 := by simp
    rw [hneg]
    exact binomialTMotzkinCount_of_neg t n (-1) (by norm_num)
  rw [hz, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hkk : ((((0 : ℕ)) : ℤ) + (((k + 1 : ℕ)) : ℤ) - 1) = (((k : ℕ)) : ℤ) := by push_cast; ring
  rw [hkk]

private theorem binomialTMotzkinCount_succ_deficit (t n r : ℕ) (hr : r ≤ n + 1) :
    binomialTMotzkinCount t (n + 1) ((((n + 1 : ℕ)) : ℤ) - (((r : ℕ)) : ℤ))
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        Nat.choose t ij.1 * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - (((ij.2 : ℕ)) : ℤ)) := by
  have hnat : ((((n + 1 : ℕ))) : ℤ) - ((((r : ℕ))) : ℤ) = ((((n + 1 - r : ℕ))) : ℤ) := by
    rw [← Int.natCast_sub hr]
  rw [hnat, binomialTMotzkinCount_succ_height t n (n + 1 - r),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  set m := Nat.min (t + 1) (r + 1) with hm
  have hm1 : m ≤ t + 1 := by rw [hm]; exact Nat.min_le_left _ _
  have hm2 : m ≤ r + 1 := by rw [hm]; exact Nat.min_le_right _ _
  have hF : ∀ k : ℕ, r < k →
      Nat.choose t k * binomialTMotzkinCount t n (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1) =
          0 := by
    intro k hk
    have hgt : ((((n : ℕ))) : ℤ) < ((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1 := by omega
    rw [binomialTMotzkinCount_of_gt t n _ hgt, mul_zero]
  have hCF : ∀ k : ℕ, t < k →
      Nat.choose t k * binomialTMotzkinCount t n (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1) =
          0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
  have hCG : ∀ k : ℕ, t < k →
      Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) = 0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
  have hL : (∑ k ∈ Finset.range (t + 1),
        Nat.choose t k * binomialTMotzkinCount t n
            (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1))
      = ∑ k ∈ Finset.range m,
        Nat.choose t k * binomialTMotzkinCount t n
            (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1) := by
    symm
    apply Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
    intro k hk hkn
    have hkm : k < t + 1 := Finset.mem_range.mp hk
    have hnm : m ≤ k := by
      by_contra hc
      push Not at hc
      exact hkn (Finset.mem_range.mpr hc)
    have hrk : r < k := by
      by_contra hc
      push Not at hc
      have hlt : k < m := by
        rw [hm]
        exact lt_min_iff.mpr ⟨hkm, by omega⟩
      omega
    exact hF k hrk
  have hR : (∑ k ∈ Finset.range m,
        Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)))
      = ∑ k ∈ Finset.range (r + 1),
        Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := by
    apply Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
    intro k hk hkn
    have hkm : k < r + 1 := Finset.mem_range.mp hk
    have hnm : m ≤ k := by
      by_contra hc
      push Not at hc
      exact hkn (Finset.mem_range.mpr hc)
    have htk : t < k := by
      by_contra hc
      push Not at hc
      have hlt : k < m := by
        rw [hm]
        exact lt_min_iff.mpr ⟨by omega, hkm⟩
      omega
    exact hCG k htk
  rw [hL]
  calc ∑ k ∈ Finset.range m,
        Nat.choose t k * binomialTMotzkinCount t n (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1)
      = ∑ k ∈ Finset.range m,
        Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkr : k ≤ r := by
          have hlt := Finset.mem_range.mp hk
          omega
        have he : (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1)
            = ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := by omega
        rw [he]
    _ = ∑ k ∈ Finset.range (r + 1),
        Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := hR

private theorem binomialTMotzkinDeficitPoly_coeff_top (t N : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N) :
    (binomialTMotzkinDeficitPoly t N).coeff N = 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [binomialTMotzkinDeficitPoly_coeff_succ]
  have hT : 1 ≤ t * (N' + 1) := by
    calc 1 = 1 * 1 := by ring
    _ ≤ t * (N' + 1) := Nat.mul_le_mul ht (Nat.succ_le_succ (Nat.zero_le _))
  have key := Nat.add_one_mul_choose_eq (t * (N' + 1) - 1) N'
  rw [Nat.sub_add_cancel hT] at key
  have hN' : ((((N' + 1 : ℕ))) : ℚ) ≠ 0 := by exact_mod_cast (show N' + 1 ≠ 0 by omega)
  have keyQ : ((((t * (N' + 1) : ℕ))) : ℚ) * ((((Nat.choose (t * (N' + 1) - 1) N' : ℕ))) : ℚ)
      = ((((Nat.choose (t * (N' + 1)) (N' + 1) : ℕ))) : ℚ) * ((((N' + 1 : ℕ))) : ℚ) := by
    have hcon := congrArg (Nat.cast : ℕ → ℚ) key
    simpa [Nat.cast_mul] using hcon
  have hTeq : ((((t * (N' + 1) : ℕ))) : ℚ) = (t : ℚ) * ((((N' + 1 : ℕ))) : ℚ) := by push_cast; ring
  rw [hTeq] at keyQ
  have hC : ((((Nat.choose (t * (N' + 1)) (N' + 1) : ℕ))) : ℚ)
      = (t : ℚ) * ((((Nat.choose (t * (N' + 1) - 1) N' : ℕ))) : ℚ) := by
    have keyQ2 : ((t : ℚ) * ((((Nat.choose (t * (N' + 1) - 1) N' : ℕ))) : ℚ)) *
        ((((N' + 1 : ℕ))) : ℚ)
        = ((((Nat.choose (t * (N' + 1)) (N' + 1) : ℕ))) : ℚ) * ((((N' + 1 : ℕ))) : ℚ) := by
      linear_combination keyQ
    exact (mul_right_cancel₀ hN' keyQ2).symm
  rw [hC]
  ring

private theorem binomialTMotzkinDeficitPoly_coeff_pred (t n : ℕ) (ht : 1 ≤ t) :
    (binomialTMotzkinDeficitPoly t (n + 1)).coeff n
      = ((((Nat.choose (t * (n + 1)) (n + 1) : ℕ))) : ℚ)
        / (((((t - 1) * (n + 1) + 1 : ℕ))) : ℚ) := by
  cases n with
  | zero =>
    rw [binomialTMotzkinDeficitPoly_coeff_zero]
    have e0 : (0 + 1 : ℕ) = 1 := rfl
    rw [e0, Nat.mul_one, Nat.choose_one_right, Nat.mul_one]
    have eT : t - 1 + 1 = t := Nat.sub_add_cancel ht
    rw [eT]
    have htoc : ((t : ℚ)) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    rw [div_self htoc]
  | succ m =>
    rw [binomialTMotzkinDeficitPoly_coeff_succ]
    have hT : 1 ≤ t * ((m + 1) + 1) := by
      calc 1 = 1 * 1 := by ring
      _ ≤ t * ((m + 1) + 1) := Nat.mul_le_mul ht (by omega)
    have abs1 := Nat.add_one_mul_choose_eq (t * ((m + 1) + 1) - 1) m
    rw [Nat.sub_add_cancel hT] at abs1
    have abs2 := Nat.choose_succ_right_eq (t * ((m + 1) + 1)) (m + 1)
    have hTD : t * ((m + 1) + 1) - (m + 1) = (t - 1) * ((m + 1) + 1) + 1 := by
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have hexpand : (t' + 1) * ((m + 1) + 1) = t' * ((m + 1) + 1) + ((m + 1) + 1) := by ring
      rw [hexpand, Nat.add_sub_assoc (by omega : m + 1 ≤ (m + 1) + 1)]
      have hM : ((m + 1) + 1) - (m + 1) = 1 := by omega
      rw [hM]
    have abs1c : ((((t * ((m + 1) + 1) : ℕ))) : ℚ) *
        ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ)
        = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ) * ((((m + 1 : ℕ))) : ℚ) := by
      have hcon := congrArg (Nat.cast : ℕ → ℚ) abs1
      simpa [Nat.cast_mul] using hcon
    have abs2c : ((((Nat.choose (t * ((m + 1) + 1)) ((m + 1) + 1) : ℕ))) : ℚ)
          * (((((m + 1) + 1 : ℕ))) : ℚ)
        = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
          * ((((t * ((m + 1) + 1) - (m + 1) : ℕ))) : ℚ) := by
      have hcon := congrArg (Nat.cast : ℕ → ℚ) abs2
      simpa [Nat.cast_mul] using hcon
    have hTDc : ((((t * ((m + 1) + 1) - (m + 1) : ℕ))) : ℚ)
        = (((( (t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) := by
      have hcon := congrArg (Nat.cast : ℕ → ℚ) hTD
      simpa [Nat.cast_mul, Nat.cast_add] using hcon
    have hTc : ((((t * ((m + 1) + 1) : ℕ))) : ℚ)
        = (t : ℚ) * (((((m + 1) + 1 : ℕ))) : ℚ) := by push_cast; ring
    have hDpos : (0 : ℚ) < (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) :=
      Nat.cast_pos.mpr (by omega)
    have hEpos : (0 : ℚ) < (((((m + 1) + 1 : ℕ))) : ℚ) := Nat.cast_pos.mpr (by omega)
    have hDn : (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) ≠ 0 := ne_of_gt hDpos
    have hEn : (((((m + 1) + 1 : ℕ))) : ℚ) ≠ 0 := ne_of_gt hEpos
    have step1 : ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ) * ((((m + 1 : ℕ))) : ℚ)
        = (t : ℚ) * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ)
          * (((((m + 1) + 1 : ℕ))) : ℚ) := by
      calc ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ) * ((((m + 1 : ℕ))) : ℚ)
          = ((((t * ((m + 1) + 1) : ℕ))) : ℚ)
            * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ) := abs1c.symm
        _ = (t : ℚ) * (((((m + 1) + 1 : ℕ))) : ℚ)
            * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ) := by rw [hTc]
        _ = (t : ℚ) * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ)
            * (((((m + 1) + 1 : ℕ))) : ℚ) := by ring
    have step2 : ((((Nat.choose (t * ((m + 1) + 1)) ((m + 1) + 1) : ℕ))) : ℚ)
          * (((((m + 1) + 1 : ℕ))) : ℚ)
        = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
          * (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) := by
      calc ((((Nat.choose (t * ((m + 1) + 1)) ((m + 1) + 1) : ℕ))) : ℚ)
            * (((((m + 1) + 1 : ℕ))) : ℚ)
          = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
            * ((((t * ((m + 1) + 1) - (m + 1) : ℕ))) : ℚ) := abs2c
        _ = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
            * (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) := by rw [hTDc]
    have hE1v : (((((m + 1) + 1 : ℕ))) : ℚ) - ((((m + 1 : ℕ))) : ℚ) - 1 = 0 := by
      push_cast; ring
    rw [eq_div_iff hDn]
    apply mul_right_cancel₀ hEn
    linear_combination
      (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) * step1
      - step2
      + (((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
        * (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ)) * hE1v

private theorem binomialTMotzkinCount_eq_deficitPoly_coeff (t n : ℕ) (ht : 1 ≤ t) :
    ∀ r : ℕ, r ≤ n + 1 →
      ((((binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r : ℕ))) : ℤ)) : ℕ))) : ℚ)
      = (binomialTMotzkinDeficitPoly t (n + 1)).coeff r := by
  induction n with
  | zero =>
    intro r hr
    interval_cases r
    · have h00 : ((((0 : ℕ))) : ℤ) - ((((0 : ℕ))) : ℤ) = 0 := by simp
      have eG : (0 + 1 : ℕ) = 1 := rfl
      rw [h00, binomialTMotzkinCount_zero]
      simp only [ite_true, Nat.cast_one]
      rw [eG]
      exact (binomialTMotzkinDeficitPoly_coeff_zero t 1).symm
    · have h01 : ((((0 : ℕ))) : ℤ) - ((((1 : ℕ))) : ℤ) = -1 := by simp
      have eG : (0 + 1 : ℕ) = 1 := rfl
      rw [h01, binomialTMotzkinCount_of_neg t 0 (-1) (by norm_num)]
      simp only [Nat.cast_zero]
      rw [eG]
      exact (binomialTMotzkinDeficitPoly_coeff_top t 1 ht (by omega)).symm
  | succ n ih =>
    intro r hr
    by_cases hr' : r ≤ n + 1
    · rw [binomialTMotzkinCount_succ_deficit t n r hr', Nat.cast_sum]
      have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
          ((((Nat.choose t ij.1
            * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((ij.2 : ℕ))) : ℤ)) : ℕ))) : ℚ)
          = ((((Nat.choose t ij.1 : ℕ))) : ℚ) * (binomialTMotzkinDeficitPoly t (n + 1)).coeff
              ij.2 := by
        intro ij hij
        have hj : ij.2 ≤ n + 1 := by
          have hmem := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          omega
        have hih := ih ij.2 hj
        rw [Nat.cast_mul, hih]
      have hsum : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
            ((((Nat.choose t ij.1
              * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((ij.2 : ℕ))) : ℤ)) : ℕ))) : ℚ))
          = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
            ((((Nat.choose t ij.1 : ℕ))) : ℚ) * (binomialTMotzkinDeficitPoly t (n + 1)).coeff
                ij.2 :=
        Finset.sum_congr rfl (fun ij hij => hterm ij hij)
      rw [hsum]
      have hmul : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
            ((((Nat.choose t ij.1 : ℕ))) : ℚ) * (binomialTMotzkinDeficitPoly t (n + 1)).coeff ij.2)
          = (((1 + Polynomial.X) ^ t * binomialTMotzkinDeficitPoly t (n + 1))).coeff r := by
        rw [Polynomial.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij _
        rw [Polynomial.coeff_one_add_X_pow]
      rw [hmul]
      have hG := binomialTMotzkinDeficitPoly_succ t (n + 1) ht (by omega : 1 ≤ n + 1)
      rw [hG]
    · have hrEq : r = n + 2 := by omega
      subst hrEq
      have hneg : ((((n + 1 : ℕ))) : ℤ) - ((((n + 2 : ℕ))) : ℤ) = -1 := by push_cast; ring
      rw [hneg, binomialTMotzkinCount_of_neg t (n + 1) _ (by norm_num : (-1 : ℤ) < 0),
        Nat.cast_zero]
      have htop := binomialTMotzkinDeficitPoly_coeff_top t (n + 2) ht (by omega)
      exact htop.symm

private noncomputable abbrev binomialTMotzkinPS (t : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ))

private theorem binomialTMotzkinPS_coeff (t n : ℕ) :
    (binomialTMotzkinPS t).coeff n = ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ) := by
  unfold binomialTMotzkinPS
  rw [PowerSeries.coeff_mk]

private theorem binomialTMotzkin_catalanGF_eq (t : ℕ) (ht : 1 ≤ t) :
    PowerSeries.mk (fun n => ((((Nat.choose (t * n) n : ℕ))) : ℚ) / (((((t - 1) * n + 1 : ℕ))) : ℚ))
      = 1 + PowerSeries.X * binomialTMotzkinPS t := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    have e1 : t * 0 = 0 := Nat.mul_zero t
    have e2 : (t - 1) * 0 + 1 = 1 := by omega
    simp only [PowerSeries.coeff_mk, e1, e2, Nat.choose_zero_right, Nat.cast_one, div_one]
    simp [map_add]
  | succ n =>
    rw [PowerSeries.coeff_mk]
    have hR : ((1 + PowerSeries.X * binomialTMotzkinPS t : PowerSeries ℚ)).coeff (n + 1)
        = ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ) := by
      rw [map_add]
      have h1 : ((1 : PowerSeries ℚ)).coeff (n + 1) = 0 := by simp
      rw [h1, zero_add, PowerSeries.coeff_succ_X_mul, binomialTMotzkinPS_coeff]
    rw [hR]
    have hN8 := binomialTMotzkinCount_eq_deficitPoly_coeff t n ht n (by omega : n ≤ n + 1)
    have hN7 := binomialTMotzkinDeficitPoly_coeff_pred t n ht
    have h00 : ((((n : ℕ))) : ℤ) - ((((n : ℕ))) : ℤ) = 0 := by simp
    rw [h00] at hN8
    rw [hN8, hN7]

private theorem binomialTMotzkin_fixedPoint (t : ℕ) :
    binomialTMotzkinPS t = (1 + PowerSeries.X * binomialTMotzkinPS t) ^ t := by
  have key : ∀ n : ℕ,
      (∀ m, m ≤ n → (binomialTMotzkinPS t).coeff m
        = ((1 + PowerSeries.X * binomialTMotzkinPS t) ^ t).coeff m)
      ∧ (∀ h : ℕ, ((((binomialTMotzkinCount t n ((((h : ℕ))) : ℤ) : ℕ))) : ℚ)
        = (PowerSeries.X ^ h * binomialTMotzkinPS t ^ (h + 1)).coeff n) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        have hL : (binomialTMotzkinPS t).coeff 0 = 1 := by
          rw [binomialTMotzkinPS_coeff, binomialTMotzkinCount_zero]
          simp
        have hR : ((1 + PowerSeries.X * binomialTMotzkinPS t : PowerSeries ℚ) ^ t).coeff 0
            = 1 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_add,
            PowerSeries.constantCoeff_one, map_mul, PowerSeries.constantCoeff_X, zero_mul,
            add_zero, one_pow]
        rw [hL, hR]
      · intro h
        cases h with
        | zero =>
          simp only [pow_zero, one_mul, Nat.zero_add, pow_one, binomialTMotzkinPS_coeff,
              Nat.cast_zero]
        | succ m =>
          have hne : ((((m + 1 : ℕ))) : ℤ) ≠ 0 := by
            exact_mod_cast (by omega : m + 1 ≠ 0)
          have hL : binomialTMotzkinCount t 0 (((m + 1 : ℕ)) : ℤ) = 0 := by
            rw [binomialTMotzkinCount_zero, ite_eq_right hne]
          rw [hL, Nat.cast_zero, PowerSeries.coeff_X_pow_mul']
          simp
    | succ n ih =>
      obtain ⟨ihC, ihD⟩ := ih
      have ihC' : ∀ m, m ≤ n + 1 → (binomialTMotzkinPS t).coeff m
          = ((1 + PowerSeries.X * binomialTMotzkinPS t) ^ t).coeff m := by
        intro m hm
        by_cases hm' : m ≤ n
        · exact ihC m hm'
        · have hmn : m = n + 1 := by omega
          subst hmn
          have hP : (binomialTMotzkinPS t).coeff (n + 1)
              = ∑ k ∈ Finset.range t, ((((Nat.choose t (k + 1) : ℕ))) : ℚ)
                * (PowerSeries.X ^ k * binomialTMotzkinPS t ^ (k + 1)).coeff n := by
            rw [binomialTMotzkinPS_coeff, binomialTMotzkinCount_succ_zero, Nat.cast_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [Nat.cast_mul, ihD k]
          have hshiftA := binomialTMotzkin_pow_coeff_shift_a (binomialTMotzkinPS t) t n
          rw [hP, hshiftA]
      have ihD' : ∀ h : ℕ, ((((binomialTMotzkinCount t (n + 1) ((((h : ℕ))) : ℤ) : ℕ))) : ℚ)
          = (PowerSeries.X ^ h * binomialTMotzkinPS t ^ (h + 1)).coeff (n + 1) := by
        intro h
        cases h with
        | zero =>
          simp only [pow_zero, one_mul, Nat.zero_add, pow_one, binomialTMotzkinPS_coeff,
              Nat.cast_zero]
        | succ m =>
          have hadd : ∀ k : ℕ, m + 1 + k = m + k + 1 := fun k => by ring
          have hshift := binomialTMotzkin_pow_coeff_shift_b (binomialTMotzkinPS t) t n (m + 1)
            (by omega)
          simp only [Nat.add_sub_cancel, hadd] at hshift
          have hcount : ((((binomialTMotzkinCount t (n + 1) (((((m + 1) : ℕ))) : ℤ) : ℕ))) : ℚ)
              = (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1)
                * (1 + PowerSeries.X * binomialTMotzkinPS t) ^ t).coeff (n + 1) := by
            rw [binomialTMotzkinCount_succ_height t n (m + 1), Nat.cast_sum, hshift]
            apply Finset.sum_congr rfl
            intro k _
            have hk : ((((m + 1 : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ) - 1
                = ((((m + k : ℕ))) : ℤ) := by omega
            rw [Nat.cast_mul, hk, ihD (m + k)]
          have hN10 := powerSeries_coeff_mul_congr_of_coeff_eq
            ((1 + PowerSeries.X * binomialTMotzkinPS t) ^ t)
            (binomialTMotzkinPS t)
            (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1))
            (n + 1) (fun m hm => (ihC' m hm).symm)
          have hps : binomialTMotzkinPS t ^ (m + 1 + 1)
              = binomialTMotzkinPS t ^ (m + 1) * binomialTMotzkinPS t := pow_succ _ _
          have hRHS : (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1)
              * binomialTMotzkinPS t).coeff (n + 1)
              = (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1 + 1)).coeff
                (n + 1) := by
            rw [hps, mul_assoc]
          rw [hcount, hN10, hRHS]
      exact ⟨ihC', ihD'⟩
  apply PowerSeries.ext
  intro n
  exact (key n).1 n le_rfl

/--
**Generating function of binomial Motzkin paths.** Let $t \ge 1$. A binomial $[t]$-Motzkin step
is one of $\binom{t}{k}$ differently colored steps that change the height by $1 - k$, for some
$k \in \{0, 1, \dots, t\}$. For $n \ge 0$ let $M_n$ be the number of sequences of $n$ such steps
for which, starting from height $0$, the height after the first $m$ steps is nonnegative for
every $0 \le m \le n$ and the height after all $n$ steps is $0$. Then, as formal power series
over $\mathbb{Q}$,

$$\sum_{n \ge 0} M_n z^n = C_t(z)^t, \qquad
C_t(z) = \sum_{n \ge 0} \frac{1}{(t-1)n + 1} \binom{tn}{n} z^n.$$

Proves `Wanted` entry `binomial_tMotzkin_generatingFunction`.

Source: Naiomi T. Cameron and Jillian E. McLeod, "Returns and Hills on
Generalized Dyck Paths," Journal of Integer Sequences 19 (2016), Article
16.6.1, Theorem (binomial `[t]`-Motzkin generating function), lines 987–989,
https://cs.uwaterloo.ca/journals/JIS/VOL19/McLeod/mcleod3.tex
-/
theorem binomial_tMotzkin_generatingFunction
    (t : ℕ) (ht : 1 ≤ t) :
    let Step := Σ k : Fin (t + 1), Fin (Nat.choose t k)
    let heightChange : Step → ℤ := fun s => 1 - (s.1 : ℤ)
    let pathCount : ℕ → ℕ := fun n =>
      Fintype.card {p : Fin n → Step //
        (∀ m : Fin (n + 1),
          0 ≤ ∑ i : Fin n, if i.1 < m.1 then heightChange (p i) else 0) ∧
        ∑ i : Fin n, heightChange (p i) = 0}
    let catalanGF : PowerSeries ℚ := PowerSeries.mk fun n =>
      (Nat.choose (t * n) n : ℚ) / (((t - 1) * n + 1 : ℕ) : ℚ)
    PowerSeries.mk (fun n => (pathCount n : ℚ)) = catalanGF ^ t := by
  intro Step heightChange pathCount catalanGF
  have hPS : PowerSeries.mk (fun n => (((pathCount n : ℕ)) : ℚ))
      = binomialTMotzkinPS t := rfl
  have hCG : catalanGF
      = PowerSeries.mk (fun n => ((((Nat.choose (t * n) n : ℕ))) : ℚ)
        / (((((t - 1) * n + 1 : ℕ))) : ℚ)) := rfl
  rw [hPS, hCG, binomialTMotzkin_catalanGF_eq t ht]
  exact binomialTMotzkin_fixedPoint t

end MetaMathlibExt
end
