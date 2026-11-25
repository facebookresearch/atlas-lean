/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MultipleBinomialTransform
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private theorem falling_comp (j l : ℤ) (a : ℕ → ℤ) (n : ℕ) :
    fallingKBinomialTransform j (fallingKBinomialTransform l a) n =
      fallingKBinomialTransform (j + l) a n := by
  have extend : ∀ jj : ℕ, jj ∈ Finset.range (n + 1) →
      (∑ ii ∈ Finset.range (jj + 1), (Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) =
      (∑ ii ∈ Finset.range (n + 1), (Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) := by
    intro jj hjj
    have hjn : jj ≤ n := by
      have h := Finset.mem_range.mp hjj
      omega
    apply Finset.sum_subset
    · intro x hx
      have hx1 : x < jj + 1 := Finset.mem_range.mp hx
      have hx2 : x < n + 1 := by omega
      exact Finset.mem_range.mpr hx2
    · intro x hx hx2
      have hx2' : ¬ x < jj + 1 := fun h => hx2 (Finset.mem_range.mpr h)
      have hlt : jj < x := by omega
      have hz : Nat.choose jj x = 0 := Nat.choose_eq_zero_of_lt hlt
      simp [hz]
  have step1 : ∀ jj ∈ Finset.range (n + 1),
      (Nat.choose n jj : ℤ) * j ^ (n - jj) *
        (∑ ii ∈ Finset.range (jj + 1), (Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) =
      ∑ ii ∈ Finset.range (n + 1),
        (Nat.choose n jj : ℤ) * j ^ (n - jj) *
          ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) := by
    intro jj hjj
    rw [extend jj hjj, Finset.mul_sum]
  have restr : ∀ ii : ℕ, ii ∈ Finset.range (n + 1) →
      (∑ jj ∈ Finset.range (n + 1),
        (Nat.choose n jj : ℤ) * j ^ (n - jj) *
          ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii)) =
      ∑ jj ∈ Finset.Ico ii (n + 1),
        (Nat.choose n jj : ℤ) * j ^ (n - jj) *
          ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) := by
    intro ii hii
    symm
    apply Finset.sum_subset
    · intro x hx
      have hx2 : x < n + 1 := (Finset.mem_Ico.mp hx).2
      exact Finset.mem_range.mpr hx2
    · intro x hx hx2
      have hx1 : x < n + 1 := Finset.mem_range.mp hx
      have hx2' : ¬ (ii ≤ x ∧ x < n + 1) := fun h => hx2 (Finset.mem_Ico.mpr h)
      have hlt : x < ii := by omega
      have hz : Nat.choose x ii = 0 := Nat.choose_eq_zero_of_lt hlt
      simp [hz]
  have term : ∀ ii : ℕ, ∀ jj ∈ Finset.Ico ii (n + 1),
      (Nat.choose n jj : ℤ) * j ^ (n - jj) *
        ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) =
      (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) (jj - ii) : ℤ) *
        (j ^ ((n - ii) - (jj - ii)) * l ^ (jj - ii))) * a ii := by
    intro ii jj hjj
    have hij : ii ≤ jj := (Finset.mem_Ico.mp hjj).1
    have h1z : (Nat.choose n jj : ℤ) * (Nat.choose jj ii : ℤ) =
        (Nat.choose n ii : ℤ) * (Nat.choose (n - ii) (jj - ii) : ℤ) := by
      have h1 : Nat.choose n jj * Nat.choose jj ii =
          Nat.choose n ii * (n - ii).choose (jj - ii) :=
        Nat.choose_mul hij
      exact_mod_cast h1
    have hexp : n - jj = (n - ii) - (jj - ii) := by omega
    rw [hexp]
    calc (Nat.choose n jj : ℤ) * j ^ ((n - ii) - (jj - ii)) *
            ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii)
        = ((Nat.choose n jj : ℤ) * (Nat.choose jj ii : ℤ)) *
            (j ^ ((n - ii) - (jj - ii)) * l ^ (jj - ii)) * a ii := by ring
      _ = ((Nat.choose n ii : ℤ) * (Nat.choose (n - ii) (jj - ii) : ℤ)) *
            (j ^ ((n - ii) - (jj - ii)) * l ^ (jj - ii)) * a ii := by rw [h1z]
      _ = (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) (jj - ii) : ℤ) *
            (j ^ ((n - ii) - (jj - ii)) * l ^ (jj - ii))) * a ii := by ring
  have key : ∀ ii : ℕ, ii ∈ Finset.range (n + 1) →
      (∑ jj ∈ Finset.range (n + 1),
        (Nat.choose n jj : ℤ) * j ^ (n - jj) *
          ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii)) =
      (Nat.choose n ii : ℤ) * (j + l) ^ (n - ii) * a ii := by
    intro ii hii
    have hin : ii ≤ n := by
      have h := Finset.mem_range.mp hii
      omega
    have hrange : n + 1 - ii = (n - ii) + 1 := by omega
    have term2 : ∀ t ∈ Finset.range ((n - ii) + 1),
        (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) ((ii + t) - ii) : ℤ) *
          (j ^ ((n - ii) - ((ii + t) - ii)) * l ^ ((ii + t) - ii))) * a ii =
        (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) t : ℤ) *
          (j ^ ((n - ii) - t) * l ^ t)) * a ii := by
      intro t _
      have e1 : (ii + t) - ii = t := Nat.add_sub_cancel_left ii t
      rw [e1]
    have binom : (∑ t ∈ Finset.range ((n - ii) + 1),
          (Nat.choose (n - ii) t : ℤ) * (j ^ ((n - ii) - t) * l ^ t)) =
        (j + l) ^ (n - ii) := by
      have h := add_pow l j (n - ii)
      rw [add_comm l j] at h
      exact (Finset.sum_congr rfl (fun t _ => by ring)).trans h.symm
    have factor : (∑ t ∈ Finset.range ((n - ii) + 1),
          (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) t : ℤ) *
            (j ^ ((n - ii) - t) * l ^ t)) * a ii) =
        (Nat.choose n ii : ℤ) *
          (∑ t ∈ Finset.range ((n - ii) + 1),
            (Nat.choose (n - ii) t : ℤ) * (j ^ ((n - ii) - t) * l ^ t)) * a ii := by
      rw [Finset.mul_sum, Finset.sum_mul]
    calc (∑ jj ∈ Finset.range (n + 1),
            (Nat.choose n jj : ℤ) * j ^ (n - jj) *
              ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii))
        = ∑ jj ∈ Finset.Ico ii (n + 1),
            (Nat.choose n jj : ℤ) * j ^ (n - jj) *
              ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii) := restr ii hii
      _ = ∑ jj ∈ Finset.Ico ii (n + 1),
            (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) (jj - ii) : ℤ) *
              (j ^ ((n - ii) - (jj - ii)) * l ^ (jj - ii))) * a ii :=
          Finset.sum_congr rfl (term ii)
      _ = ∑ t ∈ Finset.range ((n - ii) + 1),
            (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) ((ii + t) - ii) : ℤ) *
              (j ^ ((n - ii) - ((ii + t) - ii)) * l ^ ((ii + t) - ii))) * a ii := by
          rw [Finset.sum_Ico_eq_sum_range _ ii (n + 1), hrange]
      _ = ∑ t ∈ Finset.range ((n - ii) + 1),
            (Nat.choose n ii : ℤ) * ((Nat.choose (n - ii) t : ℤ) *
              (j ^ ((n - ii) - t) * l ^ t)) * a ii :=
          Finset.sum_congr rfl term2
      _ = (Nat.choose n ii : ℤ) *
            (∑ t ∈ Finset.range ((n - ii) + 1),
              (Nat.choose (n - ii) t : ℤ) * (j ^ ((n - ii) - t) * l ^ t)) * a ii := factor
      _ = (Nat.choose n ii : ℤ) * (j + l) ^ (n - ii) * a ii := by rw [binom]
  simp only [fallingKBinomialTransform]
  trans ∑ jj ∈ Finset.range (n + 1), ∑ ii ∈ Finset.range (n + 1),
    (Nat.choose n jj : ℤ) * j ^ (n - jj) * ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii)
  · exact Finset.sum_congr rfl step1
  · trans ∑ ii ∈ Finset.range (n + 1), ∑ jj ∈ Finset.range (n + 1),
      (Nat.choose n jj : ℤ) * j ^ (n - jj) * ((Nat.choose jj ii : ℤ) * l ^ (jj - ii) * a ii)
    · exact Finset.sum_comm
    · exact Finset.sum_congr rfl (fun ii hii => key ii hii)

private theorem falling_zero (a : ℕ → ℤ) :
    fallingKBinomialTransform 0 a = a := by
  funext n
  simp only [fallingKBinomialTransform]
  have hmain : (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (0 : ℤ) ^ (n - i) * a i) =
      (Nat.choose n n : ℤ) * (0 : ℤ) ^ (n - n) * a n := by
    have h1 : ∀ b ∈ Finset.range (n + 1), b ≠ n →
        (Nat.choose n b : ℤ) * (0 : ℤ) ^ (n - b) * a b = 0 := by
      intro b hb hne
      have hb1 : b < n + 1 := Finset.mem_range.mp hb
      have hlt : b < n := by omega
      have hz : (0 : ℤ) ^ (n - b) = 0 := zero_pow (by omega)
      simp [hz]
    have h2 : n ∉ Finset.range (n + 1) →
        (Nat.choose n n : ℤ) * (0 : ℤ) ^ (n - n) * a n = 0 := by
      intro hcon
      exact absurd (Finset.mem_range.mpr (by omega : n < n + 1)) hcon
    exact Finset.sum_eq_single n h1 h2
  rw [hmain]
  simp

private theorem multiple_eq_falling (m : ℕ) (a : ℕ → ℤ) :
    multipleBinomialTransform m a = fallingKBinomialTransform (m : ℤ) a := by
  induction m with
  | zero =>
    simp only [multipleBinomialTransform, Nat.cast_zero]
    exact (falling_zero a).symm
  | succ m ih =>
    funext n
    simp only [multipleBinomialTransform, binomialTransform]
    rw [ih]
    have e3 := falling_comp 1 (m : ℤ) a n
    have ecast : ((m + 1 : ℕ) : ℤ) = 1 + (m : ℤ) := by push_cast; ring
    rw [ecast]
    exact e3

private theorem iterate_neg_eq_falling (m : ℕ) (a : ℕ → ℤ) :
    Nat.iterate (fallingKBinomialTransform (-1)) m a =
      fallingKBinomialTransform (-(m : ℤ)) a := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, neg_zero]
    show a = fallingKBinomialTransform 0 a
    exact (falling_zero a).symm
  | succ m ih =>
    funext n
    rw [Function.iterate_succ_apply']
    rw [ih]
    have e3 := falling_comp (-1) (-(m : ℤ)) a n
    have ecast : (-((m + 1 : ℕ) : ℤ)) = (-1) + (-(m : ℤ)) := by push_cast; ring
    rw [ecast]
    exact e3

/--
**The k-fold binomial transform is the falling k-binomial transform.** For every integer
sequence $a$ and every integer $k$: if $k \ge 0$, applying the binomial transform $k$ times to
$a$ gives the falling $k$-binomial transform of $a$; if $k < 0$, applying the inverse binomial
transform (the falling $(-1)$-binomial transform) $-k$ times to $a$ gives the falling
$k$-binomial transform of $a$. In both cases the equality is one of integer sequences.

Source: Michael Z. Spivey and Laura L. Steil, "The k-Binomial Transforms and
the Hankel Transform", Journal of Integer Sequences 9 (2006), Article 06.1.1, Theorem
`falling_equiv`, lines 636-640,
<https://cs.uwaterloo.ca/journals/JIS/VOL9/Spivey/spivey7.tex>.

Proves `Wanted` entry `falling_equiv`.
-/
theorem falling_equiv
    (a : ℕ → ℤ) (k : ℤ) :
    (if 0 ≤ k then multipleBinomialTransform k.toNat a
      else Nat.iterate (fallingKBinomialTransform (-1)) (-k).toNat a) =
      fallingKBinomialTransform k a := by
  by_cases h : 0 ≤ k
  · simp only [h, ite_true]
    have e := multiple_eq_falling k.toNat a
    have hk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg h
    rw [hk] at e
    exact e
  · simp only [h, ite_false]
    have e := iterate_neg_eq_falling (-k).toNat a
    have hk : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    rw [hk] at e
    have hk2 : (- -k) = k := neg_neg k
    rw [hk2] at e
    exact e

end MetaMathlibExt
