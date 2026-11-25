/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Bell Number Convolution Identity -/

private lemma bell_range (j : ℕ) :
    (Nat.bell (j + 1) : ℤ) =
      ∑ t ∈ Finset.range (j + 1), ((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ) := by
  have h := Nat.bell_succ' j
  have h2 : (Nat.bell (j + 1) : ℤ) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
        (((Nat.choose j ij.1 : ℕ)) : ℤ) * ((Nat.bell ij.2 : ℕ) : ℤ) := by
    calc ((Nat.bell (j + 1) : ℕ) : ℤ)
        = (((∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
          Nat.choose j ij.1 * Nat.bell ij.2 : ℕ)) : ℤ) := by rw [h]
      _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
          (((Nat.choose j ij.1 : ℕ)) : ℤ) * ((Nat.bell ij.2 : ℕ) : ℤ) := by
            rw [Nat.cast_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [Nat.cast_mul]
  have h3 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (((Nat.choose j a : ℕ)) : ℤ) * ((Nat.bell b : ℕ) : ℤ)) j
  rw [h2, h3]
  have hrefl := Finset.sum_range_reflect
    (fun t => (((Nat.choose j t : ℕ)) : ℤ) * ((Nat.bell t : ℕ) : ℤ)) (j + 1)
  rw [← hrefl]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by
    simp [Finset.mem_range] at hk
    omega
  rw [show j + 1 - 1 - k = j - k from by omega, Nat.choose_symm hkj]

-- Recurrence for the inner Stirling-weighted sum, from `stirlingFirst_succ_succ`.
private lemma inner_rec (n p : ℕ) :
    ∑ m ∈ Finset.range (p + 1 + 1),
        ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (p + 1 - m) * (Nat.stirlingFirst (p + 1) m : ℤ)))
    = (∑ m ∈ Finset.range (p + 1),
        ((Nat.bell (n + 1 + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))))
      - (p : ℤ) * (∑ m ∈ Finset.range (p + 1),
        ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ)))) := by
  have hz0 : Nat.stirlingFirst (p + 1) 0 = 0 := Nat.stirlingFirst_succ_zero p
  have hrec : ∀ j : ℕ, Nat.stirlingFirst (p + 1) (j + 1)
      = p * Nat.stirlingFirst p (j + 1) + Nat.stirlingFirst p j :=
    fun j => Nat.stirlingFirst_succ_succ p j
  have e1 : (∑ m ∈ Finset.range (p + 1 + 1),
        ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (p + 1 - m) * (Nat.stirlingFirst (p + 1) m : ℤ))))
      = (∑ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + (j + 1)) : ℤ) *
            ((-1 : ℤ) ^ (p + 1 - (j + 1)) * (Nat.stirlingFirst (p + 1) (j + 1) : ℤ))))
        + ((Nat.bell (n + 0) : ℤ) * ((-1 : ℤ) ^ (p + 1 - 0) * (Nat.stirlingFirst (p + 1) 0 : ℤ))) :=
    Finset.sum_range_succ' _ (p + 1)
  have e2 : ((Nat.bell (n + 0) : ℤ) *
      ((-1 : ℤ) ^ (p + 1 - 0) * (Nat.stirlingFirst (p + 1) 0 : ℤ))) = 0 := by
    rw [hz0]; simp
  have hterm : ∀ j ∈ Finset.range (p + 1),
      ((Nat.bell (n + (j + 1)) : ℤ) *
          ((-1 : ℤ) ^ (p + 1 - (j + 1)) * (Nat.stirlingFirst (p + 1) (j + 1) : ℤ)))
      = ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p j : ℤ)))
        + (p : ℤ) * (((Nat.bell (n + 1 + j) : ℤ) *
            ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ)))) := by
    intro j _
    have hexp : p + 1 - (j + 1) = p - j := by omega
    have hn : n + (j + 1) = n + 1 + j := by omega
    rw [hexp, hn, hrec j]
    push_cast
    ring
  have e3 : (∑ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + (j + 1)) : ℤ) *
            ((-1 : ℤ) ^ (p + 1 - (j + 1)) * (Nat.stirlingFirst (p + 1) (j + 1) : ℤ))))
      = (∑ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p j : ℤ))))
        + (p : ℤ) * (∑ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + 1 + j) : ℤ) *
            ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ)))) := by
    have hstep : ∀ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + (j + 1)) : ℤ) *
            ((-1 : ℤ) ^ (p + 1 - (j + 1)) * (Nat.stirlingFirst (p + 1) (j + 1) : ℤ)))
        = (((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p j : ℤ)))
          + (p : ℤ) * (((Nat.bell (n + 1 + j) : ℤ) *
              ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ))))) :=
      hterm
    calc (∑ j ∈ Finset.range (p + 1),
          ((Nat.bell (n + (j + 1)) : ℤ) *
              ((-1 : ℤ) ^ (p + 1 - (j + 1)) * (Nat.stirlingFirst (p + 1) (j + 1) : ℤ))))
        = ∑ j ∈ Finset.range (p + 1),
          ((((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p j : ℤ)))
            + (p : ℤ) * (((Nat.bell (n + 1 + j) : ℤ) *
                ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ)))))) :=
          Finset.sum_congr rfl hstep
      _ = (∑ j ∈ Finset.range (p + 1),
          ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p j : ℤ))))
          + (∑ j ∈ Finset.range (p + 1),
          ((p : ℤ) * (((Nat.bell (n + 1 + j) : ℤ) *
              ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ)))))) :=
          Finset.sum_add_distrib
      _ = (∑ j ∈ Finset.range (p + 1),
          ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p j : ℤ))))
          + (p : ℤ) * (∑ j ∈ Finset.range (p + 1),
          ((Nat.bell (n + 1 + j) : ℤ) *
              ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ)))) := by
          rw [Finset.mul_sum]
  have hclt : Nat.stirlingFirst p (p + 1) = 0 :=
    Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self p)
  have eKp : ((Nat.bell (n + 1 + p) : ℤ) *
      ((-1 : ℤ) ^ (p - p) * (Nat.stirlingFirst p (p + 1) : ℤ))) = 0 := by
    rw [hclt]; simp
  have eKpeel : (∑ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ))))
      = (∑ j ∈ Finset.range p,
        ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ))))
        + ((Nat.bell (n + 1 + p) : ℤ) * ((-1 : ℤ) ^ (p - p) * (Nat.stirlingFirst p (p + 1) : ℤ))) :=
    Finset.sum_range_succ _ p
  have eKneg : ∀ j ∈ Finset.range p,
      ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ)))
      = -(((Nat.bell (n + (j + 1)) : ℤ) *
          ((-1 : ℤ) ^ (p - (j + 1)) * (Nat.stirlingFirst p (j + 1) : ℤ)))) := by
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hexp : p - j = (p - (j + 1)) + 1 := by omega
    have hn : n + 1 + j = n + (j + 1) := by omega
    rw [hexp, hn, pow_succ]
    ring
  have eApeel : (∑ m ∈ Finset.range (p + 1),
        ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))))
      = (∑ j ∈ Finset.range p,
        ((Nat.bell (n + (j + 1)) : ℤ) *
            ((-1 : ℤ) ^ (p - (j + 1)) * (Nat.stirlingFirst p (j + 1) : ℤ))))
        + ((Nat.bell (n + 0) : ℤ) * ((-1 : ℤ) ^ (p - 0) * (Nat.stirlingFirst p 0 : ℤ))) :=
    Finset.sum_range_succ' _ p
  have e5 : (∑ j ∈ Finset.range (p + 1),
        ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ))))
      = -((∑ m ∈ Finset.range (p + 1),
        ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))))
        - ((Nat.bell (n + 0) : ℤ) * ((-1 : ℤ) ^ (p - 0) * (Nat.stirlingFirst p 0 : ℤ)))) := by
    have hneg : (∑ j ∈ Finset.range p,
          ((Nat.bell (n + 1 + j) : ℤ) * ((-1 : ℤ) ^ (p - j) * (Nat.stirlingFirst p (j + 1) : ℤ))))
        = ∑ j ∈ Finset.range p,
          (-(((Nat.bell (n + (j + 1)) : ℤ) *
              ((-1 : ℤ) ^ (p - (j + 1)) * (Nat.stirlingFirst p (j + 1) : ℤ))))) :=
      Finset.sum_congr rfl eKneg
    rw [eKpeel, eKp, add_zero, eApeel, hneg, Finset.sum_neg_distrib, add_sub_cancel_right]
  have hp0 : (p : ℤ) * (Nat.stirlingFirst p 0 : ℤ) = 0 := by
    by_cases hp : p = 0
    · subst hp; simp
    · have h0 : Nat.stirlingFirst p 0 = 0 := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
        exact Nat.stirlingFirst_succ_zero q
      rw [h0]; simp
  have e6 : (p : ℤ) * ((Nat.bell (n + 0) : ℤ) *
      ((-1 : ℤ) ^ (p - 0) * (Nat.stirlingFirst p 0 : ℤ))) = 0 := by
    have hrr : (p : ℤ) * ((Nat.bell (n + 0) : ℤ) *
        ((-1 : ℤ) ^ (p - 0) * (Nat.stirlingFirst p 0 : ℤ)))
        = ((Nat.bell (n + 0) : ℤ) * (-1 : ℤ) ^ (p - 0)) * ((p : ℤ) *
            (Nat.stirlingFirst p 0 : ℤ)) := by ring
    rw [hrr, hp0, mul_zero]
  rw [e1, e2, add_zero, e3, e5]
  linear_combination e6


-- Binomial inversion kernel: choose_mul + binomial theorem.
private lemma choose_pow_mul (n t : ℕ) (a b : ℤ) (ht : t ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * a ^ (n - k) * (((Nat.choose k t : ℕ) : ℤ) * b ^ (k - t))))
    = ((Nat.choose n t : ℕ) : ℤ) * (a + b) ^ (n - t) := by
  have htn1 : t ≤ n + 1 := by omega
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => (((Nat.choose n k : ℕ) : ℤ) * a ^ (n - k) *
        (((Nat.choose k t : ℕ) : ℤ) * b ^ (k - t)))) htn1
  have hvan : (∑ k ∈ Finset.range t,
      (((Nat.choose n k : ℕ) : ℤ) * a ^ (n - k) *
          (((Nat.choose k t : ℕ) : ℤ) * b ^ (k - t)))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkt : k < t := Finset.mem_range.mp hk
    rw [Nat.choose_eq_zero_of_lt hkt]; simp
  have hIco : (∑ k ∈ Finset.range (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * a ^ (n - k) * (((Nat.choose k t : ℕ) : ℤ) * b ^ (k - t))))
      = ∑ k ∈ Finset.Ico t (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * a ^ (n - k) * (((Nat.choose k t : ℕ) : ℤ) * b ^ (k - t))) := by
    rw [← hsplit, hvan, zero_add]
  have hIco2 : (∑ k ∈ Finset.Ico t (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * a ^ (n - k) * (((Nat.choose k t : ℕ) : ℤ) * b ^ (k - t))))
      = ∑ i ∈ Finset.range (n + 1 - t),
      (((Nat.choose n (t + i) : ℕ) : ℤ) * a ^ (n - (t + i)) *
          (((Nat.choose (t + i) t : ℕ) : ℤ) * b ^ (t + i - t))) :=
    Finset.sum_Ico_eq_sum_range _ t (n + 1)
  have hrange : n + 1 - t = (n - t) + 1 := by omega
  have hterm : ∀ i ∈ Finset.range ((n - t) + 1),
      (((Nat.choose n (t + i) : ℕ) : ℤ) * a ^ (n - (t + i)) *
          (((Nat.choose (t + i) t : ℕ) : ℤ) * b ^ (t + i - t)))
      = ((Nat.choose n t : ℕ) : ℤ) * (((Nat.choose (n - t) i : ℕ) : ℤ) * a ^ ((n - t) - i) *
          b ^ i) := by
    intro i hi
    have hi2 : i ≤ n - t := by
      have := Finset.mem_range.mp hi
      omega
    have hti : t ≤ t + i := Nat.le_add_right t i
    have htin : t + i ≤ n := by omega
    have hcm : Nat.choose n (t + i) * Nat.choose (t + i) t
        = Nat.choose n t * Nat.choose (n - t) ((t + i) - t) :=
      Nat.choose_mul (n := n) (k := t + i) (s := t) hti
    have hsub : (t + i) - t = i := by omega
    have hchoose : Nat.choose n (t + i) * Nat.choose (t + i) t
        = Nat.choose n t * Nat.choose (n - t) i := by
      rw [hsub] at hcm
      exact hcm
    have hexp1 : n - (t + i) = (n - t) - i := by omega
    have hexp2 : t + i - t = i := by omega
    rw [hexp1, hexp2]
    have hcast : ((((Nat.choose n (t + i) : ℕ)) : ℤ) * (((Nat.choose (t + i) t : ℕ)) : ℤ))
        = (((Nat.choose n t : ℕ)) : ℤ) * (((Nat.choose (n - t) i : ℕ)) : ℤ) := by
      exact_mod_cast hchoose
    calc (((Nat.choose n (t + i) : ℕ) : ℤ) * a ^ ((n - t) - i) *
        (((Nat.choose (t + i) t : ℕ) : ℤ) * b ^ i))
        = ((((Nat.choose n (t + i) : ℕ)) : ℤ) * (((Nat.choose (t + i) t : ℕ)) : ℤ))
          * (a ^ ((n - t) - i) * b ^ i) := by ring
      _ = ((((Nat.choose n t : ℕ)) : ℤ) * (((Nat.choose (n - t) i : ℕ)) : ℤ))
          * (a ^ ((n - t) - i) * b ^ i) := by rw [hcast]
      _ = ((Nat.choose n t : ℕ) : ℤ) * (((Nat.choose (n - t) i : ℕ) : ℤ) * a ^ ((n - t) - i) *
          b ^ i) := by ring
  have hbin := add_pow b a (n - t)
  rw [hIco, hIco2, hrange]
  have hsum : (∑ i ∈ Finset.range ((n - t) + 1),
      (((Nat.choose n (t + i) : ℕ) : ℤ) * a ^ (n - (t + i)) *
          (((Nat.choose (t + i) t : ℕ) : ℤ) * b ^ (t + i - t))))
      = ∑ i ∈ Finset.range ((n - t) + 1),
        ((Nat.choose n t : ℕ) : ℤ) * (((Nat.choose (n - t) i : ℕ) : ℤ) * a ^ ((n - t) - i) *
            b ^ i) :=
    Finset.sum_congr rfl hterm
  rw [hsum, ← Finset.mul_sum]
  have hterm2 : ∀ i ∈ Finset.range ((n - t) + 1),
      (((Nat.choose (n - t) i : ℕ) : ℤ) * a ^ ((n - t) - i) * b ^ i)
      = b ^ i * a ^ ((n - t) - i) * ((Nat.choose (n - t) i : ℕ) : ℤ) := by
    intro i _
    ring
  have hsum2 : (∑ i ∈ Finset.range ((n - t) + 1),
      (((Nat.choose (n - t) i : ℕ) : ℤ) * a ^ ((n - t) - i) * b ^ i))
      = ∑ m ∈ Finset.range ((n - t) + 1), (b ^ m * a ^ ((n - t) - m) *
          ((Nat.choose (n - t) m : ℕ) : ℤ)) :=
    Finset.sum_congr rfl hterm2
  rw [hsum2, ← hbin, add_comm b a]

-- Expand the Bell recurrence inside the outer sum and swap summation order.
private lemma outer_expand (n p : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * ((p : ℤ) + 1) ^ (n - k) * (Nat.bell k : ℤ)))
    = ∑ j ∈ Finset.range (n + 1),
      (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) * (Nat.bell (j + 1) : ℤ)) := by
  have hexpand : ∀ j ∈ Finset.range (n + 1),
      ((Nat.bell (j + 1) : ℤ))
      = ∑ t ∈ Finset.range (j + 1), (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ)) :=
    fun j _ => bell_range j
  have hstep1 : (∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) * (Nat.bell (j + 1) : ℤ)))
      = ∑ j ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (j + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hexpand j hj, Finset.mul_sum]
  have hextend : ∀ j ∈ Finset.range (n + 1),
      (∑ t ∈ Finset.range (j + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))))
      = ∑ t ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))) := by
    intro j hj
    have hjn : j ≤ n := by
      have hmem := Finset.mem_range.mp hj
      omega
    apply Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ n + 1))
    intro t ht hnt
    have hjt : j < t := by
      have ht1 := Finset.mem_range.mp ht
      rw [Finset.mem_range] at hnt
      omega
    rw [Nat.choose_eq_zero_of_lt hjt]; simp
  have hwide : (∑ j ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (j + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))))
      = ∑ j ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))) :=
    Finset.sum_congr rfl hextend
  have hfactor : ∀ t ∈ Finset.range (n + 1),
      (∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))))
      = (∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) * ((Nat.choose j t : ℕ) : ℤ)))
        * (Nat.bell t : ℤ) := by
    intro t _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinner : ∀ t ∈ Finset.range (n + 1),
      (∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) * ((Nat.choose j t : ℕ) : ℤ)))
      = ((Nat.choose n t : ℕ) : ℤ) * ((p : ℤ) + 1) ^ (n - t) := by
    intro t ht
    have htn : t ≤ n := by
      have hmem := Finset.mem_range.mp ht
      omega
    have h := choose_pow_mul n t (p : ℤ) 1 htn
    simp only [one_pow, mul_one] at h
    exact h
  have hfactored : (∑ t ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) *
            (((Nat.choose j t : ℕ) : ℤ) * (Nat.bell t : ℤ))))
      = ∑ t ∈ Finset.range (n + 1),
        (((Nat.choose n t : ℕ) : ℤ) * ((p : ℤ) + 1) ^ (n - t) * (Nat.bell t : ℤ)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hfactor t ht, hinner t ht]
  rw [hstep1, hwide, Finset.sum_comm, hfactored]

-- Shift identity for the outer sum, from `bell_range` and `choose_succ_succ`.
private lemma outer_shift (n p : ℕ) :
    (∑ k ∈ Finset.range (n + 1 + 1),
      (((Nat.choose (n + 1) k : ℕ) : ℤ) * (p : ℤ) ^ (n + 1 - k) * (Nat.bell k : ℤ)))
    = (p : ℤ) * (∑ k ∈ Finset.range (n + 1),
        (((Nat.choose n k : ℕ) : ℤ) * (p : ℤ) ^ (n - k) * (Nat.bell k : ℤ)))
      + ∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℕ) : ℤ) * (p : ℤ) ^ (n - j) * (Nat.bell (j + 1) : ℤ)) := by
  have eFpeel : (∑ k ∈ Finset.range (n + 1 + 1),
        (((Nat.choose (n + 1) k : ℕ) : ℤ) * (p : ℤ) ^ (n + 1 - k) * (Nat.bell k : ℤ)))
      = (∑ k ∈ Finset.range (n + 1),
        (((Nat.choose (n + 1) (k + 1) : ℕ) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) *
            (Nat.bell (k + 1) : ℤ)))
        + ((((Nat.choose (n + 1) 0 : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1) * ((Nat.bell 0 : ℕ) : ℤ)) := by
    have h := Finset.sum_range_succ'
      (fun k => (((Nat.choose (n + 1) k : ℕ) : ℤ) * (p : ℤ) ^ (n + 1 - k) * (Nat.bell k : ℤ)))
      (n + 1)
    simpa [show n + 1 - 0 = n + 1 from by omega] using h
  have hterm0 : ((((Nat.choose (n + 1) 0 : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1) * ((Nat.bell 0 : ℕ) : ℤ))
      = (p : ℤ) ^ (n + 1) := by
    simp only [Nat.choose_zero_right, Nat.bell_zero, Nat.cast_one, one_mul, mul_one]
  have hcsplit : ∀ k ∈ Finset.range (n + 1),
      ((((Nat.choose (n + 1) (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) *
          (Nat.bell (k + 1) : ℤ))
      = ((((Nat.choose n k : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ))
        + ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) *
            (Nat.bell (k + 1) : ℤ)) := by
    intro k _
    have hcc : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
      Nat.choose_succ_succ n k
    rw [hcc]
    push_cast
    ring
  have hsplitSum : (∑ k ∈ Finset.range (n + 1),
        ((((Nat.choose (n + 1) (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) *
            (Nat.bell (k + 1) : ℤ)))
      = (∑ k ∈ Finset.range (n + 1),
        ((((Nat.choose n k : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ)))
        + (∑ k ∈ Finset.range (n + 1),
        ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) *
            (Nat.bell (k + 1) : ℤ))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hcsplit
  have hfirst : (∑ k ∈ Finset.range (n + 1),
        ((((Nat.choose n k : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ)))
      = ∑ j ∈ Finset.range (n + 1),
        ((((Nat.choose n j : ℕ)) : ℤ) * (p : ℤ) ^ (n - j) * (Nat.bell (j + 1) : ℤ)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show n + 1 - (k + 1) = n - k from by omega]
  have hlast : ((((Nat.choose n (n + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (n + 1)) *
      (Nat.bell (n + 1) : ℤ)) = 0 := by
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [Nat.choose_eq_zero_of_lt hlt]; simp
  have hS2peel : (∑ k ∈ Finset.range (n + 1),
        ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ)))
      = (∑ k ∈ Finset.range n,
        ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ)))
        + ((((Nat.choose n (n + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (n + 1)) *
            (Nat.bell (n + 1) : ℤ)) :=
    Finset.sum_range_succ _ n
  have eFpeel2 : (∑ k ∈ Finset.range (n + 1),
        (((Nat.choose n k : ℕ) : ℤ) * (p : ℤ) ^ (n - k) * (Nat.bell k : ℤ)))
      = (∑ k ∈ Finset.range n,
        (((Nat.choose n (k + 1) : ℕ) : ℤ) * (p : ℤ) ^ (n - (k + 1)) * (Nat.bell (k + 1) : ℤ)))
        + ((((Nat.choose n 0 : ℕ)) : ℤ) * (p : ℤ) ^ (n - 0) * ((Nat.bell 0 : ℕ) : ℤ)) :=
    Finset.sum_range_succ' _ n
  have hg0 : (p : ℤ) * ((((Nat.choose n 0 : ℕ)) : ℤ) * (p : ℤ) ^ (n - 0) * ((Nat.bell 0 : ℕ) : ℤ))
      = (p : ℤ) ^ (n + 1) := by
    have hc0 : Nat.choose n 0 = 1 := Nat.choose_zero_right n
    have hb0 : Nat.bell 0 = 1 := Nat.bell_zero
    rw [hc0, hb0]
    simp only [Nat.cast_one, Nat.sub_zero, mul_one, one_mul]
    exact (pow_succ' ((p : ℤ)) n).symm
  have hmatch : ∀ k ∈ Finset.range n,
      ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ))
      = (p : ℤ) * ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n - (k + 1)) *
          (Nat.bell (k + 1) : ℤ)) := by
    intro k hk
    have hkk : k + 1 ≤ n := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hexp : n - k = (n - (k + 1)) + 1 := by omega
    rw [show n + 1 - (k + 1) = n - k from by omega, hexp, pow_succ']
    ring
  have hmatchSum : (∑ k ∈ Finset.range n,
        ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n + 1 - (k + 1)) * (Nat.bell (k + 1) : ℤ)))
      = (p : ℤ) * (∑ k ∈ Finset.range n,
        ((((Nat.choose n (k + 1) : ℕ)) : ℤ) * (p : ℤ) ^ (n - (k + 1)) *
            (Nat.bell (k + 1) : ℤ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hmatch
  rw [eFpeel, hsplitSum, hfirst, hS2peel, hlast, add_zero, hterm0, eFpeel2, mul_add, hg0, hmatchSum]
  ring

-- Recurrence for the outer Bell-weighted sum.
private lemma outer_rec (n p : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * ((p : ℤ) + 1) ^ (n - k) * (Nat.bell k : ℤ)))
    = (∑ k ∈ Finset.range (n + 1 + 1),
        (((Nat.choose (n + 1) k : ℕ) : ℤ) * (p : ℤ) ^ (n + 1 - k) * (Nat.bell k : ℤ)))
      - (p : ℤ) * (∑ k ∈ Finset.range (n + 1),
        (((Nat.choose n k : ℕ) : ℤ) * (p : ℤ) ^ (n - k) * (Nat.bell k : ℤ))) := by
  rw [outer_expand n p, outer_shift n p]
  ring

-- The inner Stirling-weighted sum equals the Bell-weighted power sum.
private lemma key (n p : ℕ) :
    (∑ m ∈ Finset.range (p + 1),
      ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))))
    = ∑ k ∈ Finset.range (n + 1),
      (((Nat.choose n k : ℕ) : ℤ) * (p : ℤ) ^ (n - k) * (Nat.bell k : ℤ)) := by
  induction p generalizing n with
  | zero =>
    have h1 : (∑ m ∈ Finset.range (0 + 1),
        ((Nat.bell (n + m) : ℤ) * ((-1 : ℤ) ^ (0 - m) * (Nat.stirlingFirst 0 m : ℤ))))
        = (Nat.bell n : ℤ) := by
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      simp [Nat.stirlingFirst_zero]
    have hmain : ((((Nat.choose n n : ℕ)) : ℤ) * ((0 : ℤ)) ^ (n - n) * (Nat.bell n : ℤ))
        = (Nat.bell n : ℤ) := by
      simp
    have h2 : (∑ k ∈ Finset.range (n + 1),
        (((Nat.choose n k : ℕ) : ℤ) * ((0 : ℤ)) ^ (n - k) * (Nat.bell k : ℤ)))
        = (Nat.bell n : ℤ) := by
      refine (Finset.sum_eq_single n ?_ ?_).trans hmain
      · intro k hk hkn
        have hkn2 : k < n := by
          have hmem := Finset.mem_range.mp hk
          omega
        have hne : n - k ≠ 0 := by omega
        rw [zero_pow hne]
        simp
      · intro hn
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn
    exact h1.trans h2.symm
  | succ p ih =>
    rw [inner_rec n p, Nat.cast_add, Nat.cast_one, outer_rec n p, ih (n + 1), ih n]

/--
**Gould–Quaintance double-sum formula for Bell numbers.** Write $B_n$ for the $n$-th Bell
number and $s(p, m) = (-1)^{p-m} {p \brack m}$ for the signed Stirling number of the first kind,
where ${p \brack m}$ is the number of permutations of $p$ elements with exactly $m$ cycles. For all
natural numbers $n$ and $p$, with the convention $0^0 = 1$,
$$B_n = \sum_{k=0}^{n} (-p)^{n-k} \binom{n}{k} \sum_{m=0}^{p} B_{k+m}\, s(p, m).$$

The source states the formula for $p \ge 1$; with $0^0 = 1$ it also holds for $p = 0$.

Proves `Wanted` entry `bell_eq_signed_stirlingFirst_convolution`.

Source: H. W. Gould and Jocelyn Quaintance, "Implications of Spivey's Bell
Number Formula," Journal of Integer Sequences 11 (2008), Article 08.3.7,
Theorem, equation (E:4), lines 177–182,
https://cs.uwaterloo.ca/journals/JIS/VOL11/Gould/gould35.tex
-/
theorem bell_eq_signed_stirlingFirst_convolution
    (n p : ℕ) :
    (Nat.bell n : ℤ) =
      ∑ k ∈ Finset.range (n + 1),
        (-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (∑ m ∈ Finset.range (p + 1),
            (Nat.bell (k + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))) := by
  have hkey : ∀ k : ℕ,
      (∑ m ∈ Finset.range (p + 1),
        ((Nat.bell (k + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))))
      = ∑ t ∈ Finset.range (k + 1),
        (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ)) :=
    fun k => key k p
  have houter : (∑ k ∈ Finset.range (n + 1),
        (-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (∑ m ∈ Finset.range (p + 1),
            (Nat.bell (k + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))))
      = ∑ k ∈ Finset.range (n + 1),
        (-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (∑ t ∈ Finset.range (k + 1),
            (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ))) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hkey k]
  have hextend : ∀ k ∈ Finset.range (n + 1),
      (∑ t ∈ Finset.range (k + 1),
        (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ)))
      = ∑ t ∈ Finset.range (n + 1),
        (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ)) := by
    intro k hk
    have hkn : k ≤ n := by
      have hmem := Finset.mem_range.mp hk
      omega
    apply Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ n + 1))
    intro t ht hnt
    have hkt : k < t := by
      have ht1 := Finset.mem_range.mp ht
      rw [Finset.mem_range] at hnt
      omega
    rw [Nat.choose_eq_zero_of_lt hkt]; simp
  have hwide : (∑ k ∈ Finset.range (n + 1),
        (-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (∑ t ∈ Finset.range (k + 1),
            (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ))))
      = ∑ k ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1),
        ((-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hextend k hk, Finset.mul_sum]
  have hper : ∀ t ∈ Finset.range (n + 1),
      (∑ k ∈ Finset.range (n + 1),
        ((-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ))))
      = ((Nat.choose n t : ℕ) : ℤ) * (0 : ℤ) ^ (n - t) * (Nat.bell t : ℤ) := by
    intro t ht
    have htn : t ≤ n := by
      have hmem := Finset.mem_range.mp ht
      omega
    have h := choose_pow_mul n t (-(p : ℤ)) (p : ℤ) htn
    have h0 : (-(p : ℤ)) + (p : ℤ) = 0 := neg_add_cancel _
    rw [h0] at h
    have hfactor : (∑ k ∈ Finset.range (n + 1),
          ((-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
            (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ))))
        = (∑ k ∈ Finset.range (n + 1),
          (((Nat.choose n k : ℕ) : ℤ) * (-(p : ℤ)) ^ (n - k) *
            (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t))))
          * (Nat.bell t : ℤ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hfactor, h]
  have hfinal : (∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
          (((Nat.choose k t : ℕ) : ℤ) * (p : ℤ) ^ (k - t) * (Nat.bell t : ℤ))))
      = ∑ t ∈ Finset.range (n + 1),
        (((Nat.choose n t : ℕ) : ℤ) * (0 : ℤ) ^ (n - t) * (Nat.bell t : ℤ)) :=
    Finset.sum_congr rfl hper
  have hmain : ((((Nat.choose n n : ℕ)) : ℤ) * (0 : ℤ) ^ (n - n) * ((Nat.bell n : ℕ) : ℤ))
      = (Nat.bell n : ℤ) := by
    simp
  have hsingle : (∑ t ∈ Finset.range (n + 1),
        (((Nat.choose n t : ℕ) : ℤ) * (0 : ℤ) ^ (n - t) * (Nat.bell t : ℤ)))
      = (Nat.bell n : ℤ) := by
    refine (Finset.sum_eq_single n ?_ ?_).trans hmain
    · intro t ht htn
      have htn2 : t < n := by
        have hmem := Finset.mem_range.mp ht
        omega
      have hne : n - t ≠ 0 := by omega
      rw [zero_pow hne]
      simp
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn
  rw [houter, hwide, Finset.sum_comm, hfinal, hsingle]

end MetaMathlibExt
