/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private theorem touchard_catalan_rec (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := Nat.succ_mul_centralBinom_succ n
  have h3 := succ_mul_catalan_eq_centralBinom n
  have key : (n + 1) * ((n + 2) * catalan (n + 1))
      = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    linear_combination h2 + (n + 1) * h1 - 2 * (2 * n + 1) * h3
  exact mul_left_cancel₀ (by omega : n + 1 ≠ 0) key

private theorem touchard_choose_down (n k : ℕ) :
    n * (n - 1).choose k = n.choose k * (n - k) := by
  by_cases hn : n = 0
  · subst hn
    have h01 : (0 : ℕ) - 1 = 0 := by omega
    have h0k : (0 : ℕ) - k = 0 := by omega
    rw [h01, h0k, zero_mul, mul_zero]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have h := Nat.choose_mul_succ_eq m k
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    linear_combination h

private theorem touchard_choose_step (n i : ℕ) :
    n.choose (2 * i + 2) * ((2 * i + 2) * (2 * i + 1))
      = n.choose (2 * i) * ((n - 2 * i) * (n - (2 * i + 1))) := by
  have e1 := Nat.choose_succ_right_eq n (2 * i + 1)
  have e2 := Nat.choose_succ_right_eq n (2 * i)
  have r1 : 2 * i + 1 + 1 = 2 * i + 2 := by omega
  rw [r1] at e1
  linear_combination e1 * (2 * i + 1) + e2 * (n - (2 * i + 1))

/-- **Touchard's Catalan identity.** For every natural number $n$, writing
$C_k = \binom{2k}{k}/(k+1)$ for the $k$-th Catalan number,
$$C_{n+1} = \sum_{i=0}^{\lfloor n/2 \rfloor} \binom{n}{2i} 2^{n-2i} C_i.$$

Proves `Wanted` entry `touchard_catalan_identity`.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL20/Dershowitz/dersh3.tex, lines 274-277.
Grounded record `jis_grounded_8d6801e19f84ccd671cecd8e`, concept
`jis_dep_66a308b917e737cb196c1412`. File SHA-256
`f34deece6b6101298cf0abee4c3e12577a8a7db55afe76325aef6447839e0646`, exact span SHA-256
`ba2f60f14652718c971cd41bf7b6a3f069a5e835bad930bd72a403a07d400f25`. A second JIS source
prints the finite upper bound as `floor(n/2)`.
-/
theorem touchard_catalan_identity (n : Nat) :
    catalan (n + 1) =
      (Finset.range (n / 2 + 1)).sum
        (fun i => catalan i * 2 ^ (n - 2 * i) * Nat.choose n (2 * i)) := by
  set F : ℕ → ℕ → ℚ := fun m i =>
    (catalan i : ℚ) * (2 : ℚ) ^ (m - 2 * i) * (m.choose (2 * i) : ℚ) with hF
  set Z : ℕ → ℕ → ℚ := fun m i =>
    -4 * (i : ℚ) * ((i : ℚ) + 1) * F m i with hZ
  have key : ∀ m i : ℕ, 1 ≤ m →
      (m : ℚ) * (((m : ℚ) + 2) * F m i - 2 * (2 * (m : ℚ) + 1) * F (m - 1) i)
        = Z m (i + 1) - Z m i := by
    intro m i hm
    by_cases hAi : m < 2 * i
    · have h1 : m.choose (2 * i) = 0 := Nat.choose_eq_zero_of_lt hAi
      have h2 : (m - 1).choose (2 * i) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      have h3 : m.choose (2 * (i + 1)) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [hF, hZ, h1, h2, h3, Nat.cast_zero, mul_zero, sub_self]
    · by_cases hBi : m = 2 * i
      · have h2 : (m - 1).choose (2 * i) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have h3 : m.choose (2 * (i + 1)) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have hB : (m : ℚ) = 2 * (i : ℚ) := by exact_mod_cast hBi
        simp only [hF, hZ, h2, h3, Nat.cast_zero, mul_zero, sub_zero, zero_sub]
        rw [hB]
        ring
      · by_cases hC1 : 2 * (i + 1) ≤ m
        · have eSub1 : ((m - 2 * i : ℕ) : ℚ) = (m : ℚ) - 2 * (i : ℚ) := by
            have hle : 2 * i ≤ m := by omega
            rw [Nat.cast_sub hle]; simp
          have eSub2 : ((m - (2 * i + 1) : ℕ) : ℚ)
              = (m : ℚ) - (2 * (i : ℚ) + 1) := by
            have hle : 2 * i + 1 ≤ m := by omega
            rw [Nat.cast_sub hle]; simp
          have hNQ : (m : ℚ) * ((m - 1).choose (2 * i) : ℚ)
              = (m.choose (2 * i) : ℚ) * ((m : ℚ) - 2 * (i : ℚ)) := by
            have hc : ((m * (m - 1).choose (2 * i) : ℕ) : ℚ)
                = ((m.choose (2 * i) * (m - 2 * i) : ℕ) : ℚ) := by
              exact_mod_cast touchard_choose_down m (2 * i)
            push_cast at hc
            rw [eSub1] at hc
            linear_combination hc
          have hCatQ : ((i : ℚ) + 2) * (catalan (i + 1) : ℚ)
              = 2 * (2 * (i : ℚ) + 1) * (catalan i : ℚ) := by
            have hc : ((((i + 2) * catalan (i + 1) : ℕ)) : ℚ)
                = (((2 * (2 * i + 1) * catalan i : ℕ)) : ℚ) := by
              exact_mod_cast touchard_catalan_rec i
            push_cast at hc
            linear_combination hc
          have hChQ : (m.choose (2 * i + 2) : ℚ)
                * ((2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 1))
              = (m.choose (2 * i) : ℚ)
                * (((m : ℚ) - 2 * (i : ℚ)) * ((m : ℚ) - (2 * (i : ℚ) + 1))) := by
            have hc : ((m.choose (2 * i + 2) * ((2 * i + 2) * (2 * i + 1)) : ℕ) : ℚ)
                = ((m.choose (2 * i) * ((m - 2 * i) * (m - (2 * i + 1))) : ℕ) : ℚ) := by
              exact_mod_cast touchard_choose_step m i
            push_cast at hc
            rw [eSub1, eSub2] at hc
            linear_combination hc
          have hP : (2 : ℚ) ^ (m - 2 * i)
              = 2 * (2 : ℚ) ^ ((m - 1) - 2 * i) := by
            have e : m - 2 * i = ((m - 1) - 2 * i) + 1 := by omega
            rw [e, pow_succ]
            ring
          have hPw : (2 : ℚ) ^ (m - 2 * i)
              = 4 * (2 : ℚ) ^ (m - 2 * (i + 1)) := by
            have e : m - 2 * i = (m - 2 * (i + 1)) + 2 := by omega
            rw [e, pow_add]
            ring
          have hDown : 2 * (m : ℚ) * F (m - 1) i
              = ((m : ℚ) - 2 * (i : ℚ)) * F m i := by
            simp only [hF]
            linear_combination 2 * (catalan i : ℚ) * (2 : ℚ) ^ ((m - 1) - 2 * i)
                * hNQ - ((m : ℚ) - 2 * (i : ℚ)) * (catalan i : ℚ)
                * (m.choose (2 * i) : ℚ) * hP
          have hUp : 4 * ((i : ℚ) + 1) * ((i : ℚ) + 2) * F m (i + 1)
              = ((m : ℚ) - 2 * (i : ℚ)) * ((m : ℚ) - (2 * (i : ℚ) + 1))
                * F m i := by
            have eIdx : 2 * (i + 1) = 2 * i + 2 := by ring
            simp only [hF, eIdx]
            linear_combination 4 * ((i : ℚ) + 1) * (2 : ℚ) ^ (m - (2 * i + 2))
                * (m.choose (2 * i + 2) : ℚ) * hCatQ
              + 4 * (catalan i : ℚ) * (2 : ℚ) ^ (m - (2 * i + 2)) * hChQ
              - ((m : ℚ) - 2 * (i : ℚ)) * ((m : ℚ) - (2 * (i : ℚ) + 1))
                * (catalan i : ℚ) * (m.choose (2 * i) : ℚ) * hPw
          simp only [hZ]
          push_cast
          linear_combination (-(2 * (m : ℚ) + 1)) * hDown + hUp
        · have hC2 : m = 2 * i + 1 := by omega
          subst hC2
          have hB1 : F (2 * i + 1 - 1) i = (catalan i : ℚ) := by
            have e1 : 2 * i + 1 - 1 = 2 * i := by omega
            have e2 : (2 * i + 1 - 1) - 2 * i = 0 := by omega
            have e3 : (2 * i + 1 - 1).choose (2 * i) = 1 := by
              rw [e1]; exact Nat.choose_self _
            simp only [hF, e2, e3, pow_zero, Nat.cast_one, mul_one]
          have hA1 : F (2 * i + 1) i
              = (catalan i : ℚ) * 2 * (2 * (i : ℚ) + 1) := by
            have hch : (2 * i + 1).choose (2 * i) = 2 * i + 1 :=
              Nat.choose_succ_self_right (2 * i)
            have he : (2 * i + 1) - 2 * i = 1 := by omega
            simp only [hF, he, hch, pow_one]
            push_cast
            ring
          have hC1 : Z (2 * i + 1) (i + 1) = 0 := by
            have h0 : F (2 * i + 1) (i + 1) = 0 := by
              have hc : (2 * i + 1).choose (2 * (i + 1)) = 0 :=
                Nat.choose_eq_zero_of_lt (by omega)
              simp only [hF, hc, Nat.cast_zero, mul_zero]
            simp only [hZ, h0, mul_zero]
          rw [hC1]
          simp only [hZ, hA1, hB1]
          push_cast
          ring
  have hSrec : ∀ m : ℕ, 1 ≤ m →
      ((m : ℚ) + 2) * (Finset.range (m / 2 + 1)).sum (fun i => F m i)
        = 2 * (2 * (m : ℚ) + 1)
          * (Finset.range ((m - 1) / 2 + 1)).sum (fun i => F (m - 1) i) := by
    intro m hm
    have e1 : (Finset.range (m / 2 + 1)).sum
          (fun i => (m : ℚ) * (((m : ℚ) + 2) * F m i
            - 2 * (2 * (m : ℚ) + 1) * F (m - 1) i))
        = (Finset.range (m / 2 + 1)).sum (fun i => Z m (i + 1) - Z m i) :=
      Finset.sum_congr rfl (fun i _ => key m i hm)
    have eL : (Finset.range (m / 2 + 1)).sum
          (fun i => (m : ℚ) * (((m : ℚ) + 2) * F m i
            - 2 * (2 * (m : ℚ) + 1) * F (m - 1) i))
        = (m : ℚ) * (((m : ℚ) + 2) * (Finset.range (m / 2 + 1)).sum (fun i => F m i)
          - 2 * (2 * (m : ℚ) + 1)
            * (Finset.range (m / 2 + 1)).sum (fun i => F (m - 1) i)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
    have eR : (Finset.range (m / 2 + 1)).sum (fun i => Z m (i + 1) - Z m i)
        = Z m (m / 2 + 1) - Z m 0 :=
      Finset.sum_range_sub _ _
    have hZK : Z m (m / 2 + 1) = 0 := by
      have h0 : F m (m / 2 + 1) = 0 := by
        have hc : m.choose (2 * (m / 2 + 1)) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp only [hF, hc, Nat.cast_zero, mul_zero]
      simp only [hZ, h0, mul_zero]
    have hZ0 : Z m 0 = 0 := by
      simp only [hZ, Nat.cast_zero, mul_zero, zero_mul]
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have e0 : ((m : ℚ) + 2) * (Finset.range (m / 2 + 1)).sum (fun i => F m i)
          - 2 * (2 * (m : ℚ) + 1)
            * (Finset.range (m / 2 + 1)).sum (fun i => F (m - 1) i) = 0 := by
      have hX : (m : ℚ) * (((m : ℚ) + 2)
            * (Finset.range (m / 2 + 1)).sum (fun i => F m i)
            - 2 * (2 * (m : ℚ) + 1)
              * (Finset.range (m / 2 + 1)).sum (fun i => F (m - 1) i)) = 0 := by
        rw [← eL, e1, eR, hZK, hZ0, sub_self]
      rcases mul_eq_zero.mp hX with h | h
      · exact absurd h hm0
      · exact h
    have hsub : Finset.range ((m - 1) / 2 + 1) ⊆ Finset.range (m / 2 + 1) :=
      Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
    have eS : (Finset.range (m / 2 + 1)).sum (fun i => F (m - 1) i)
        = (Finset.range ((m - 1) / 2 + 1)).sum (fun i => F (m - 1) i) := by
      refine (Finset.sum_subset hsub (fun x hxK hxK' => ?_)).symm
      have hx : (m - 1) / 2 + 1 ≤ x := by
        simp only [Finset.mem_range, not_lt] at hxK'
        exact hxK'
      have h0 : F (m - 1) x = 0 := by
        have hc : (m - 1).choose (2 * x) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp only [hF, hc, Nat.cast_zero, mul_zero]
      exact h0
    linear_combination e0 + 2 * (2 * (m : ℚ) + 1) * eS
  have hmain : ∀ m : ℕ, (Finset.range (m / 2 + 1)).sum (fun i => F m i)
      = (catalan (m + 1) : ℚ) := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.zero_div, zero_add, Finset.sum_range_one, hF]
      simp [catalan_zero, catalan_one]
    | succ k ih =>
      have hrec := hSrec (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      push_cast at hrec
      have hcat : ((k : ℚ) + 1 + 2) * (catalan (k + 1 + 1) : ℚ)
          = 2 * (2 * ((k : ℚ) + 1) + 1) * (catalan (k + 1) : ℚ) := by
        exact_mod_cast touchard_catalan_rec (k + 1)
      have hpos : ((k : ℚ) + 1 + 2) ≠ 0 := by positivity
      have e : ((k : ℚ) + 1 + 2)
            * (Finset.range ((k + 1) / 2 + 1)).sum (fun i => F (k + 1) i)
          = ((k : ℚ) + 1 + 2) * (catalan (k + 1 + 1) : ℚ) := by
        linear_combination hrec - hcat + 2 * (2 * ((k : ℚ) + 1) + 1) * ih
      exact mul_left_cancel₀ hpos e
  have hfin := hmain n
  have h2 : (((Finset.range (n / 2 + 1)).sum
        (fun i => catalan i * 2 ^ (n - 2 * i) * Nat.choose n (2 * i)) : ℕ) : ℚ)
      = ((catalan (n + 1) : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    rw [← hfin]
    exact Finset.sum_congr rfl (fun i _ => by simp [hF])
  exact (Nat.cast_injective h2).symm

end MetaMathlibExt
