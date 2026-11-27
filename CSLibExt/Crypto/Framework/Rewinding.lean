/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Averaging

/-!
# The rewinding lemma

Let `X : PMF S` be a distribution on a type `S`, let `T` be a finite non-empty type, and let
`f : S → T → Bool`. Draw `x` from `X` and two challenges `y` and `y'` uniformly from `T`, all
three independently, and let `ε` be the probability that `f x y = true`. The rewinding lemma
says that `f x y = true`, `f x y' = true` and `y ≠ y'` hold together with probability at least
`ε ^ 2 - ε / |T|`.

In a security reduction `x` collects all the random choices other than the challenge `y`.
Rewinding the adversary to the point where it receives the challenge and answering it again
with a fresh challenge `y'` gives two successful runs with distinct challenges, such as two
accepting conversations of an identification protocol that share a commitment, with at least
this probability.

The probabilities are success probabilities `winProb` of games, as in the rest of the framework.
Boneh and Shoup take `S` finite; here `X` is any discrete distribution `PMF S`.

## Main results

* `sq_sub_div_card_le_winProb_rewind`: the rewinding lemma.

## References

* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017,
  Section 19.1, Lemma 19.2.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open Finset Cslib.Probability.PMF

/-- **The rewinding lemma** (Boneh and Shoup, *A Graduate Course in Applied Cryptography*,
version 0.4, Lemma 19.2). Let `X` be a distribution on a type `S`, let `T` be a finite non-empty
type, and let `f : S → T → Bool`. Draw `x` from `X` and `y` and `y'` uniformly from `T`, all three
independently, and let `ε = Pr[f x y = true]`. Then

`Pr[f x y = true ∧ f x y' = true ∧ y ≠ y'] ≥ ε ^ 2 - ε / |T|`.

Boneh and Shoup take `S` finite; the bound holds for every discrete distribution `X : PMF S`. -/
theorem sq_sub_div_card_le_winProb_rewind {S T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (X : PMF S) (f : S → T → Bool) :
    winProb (X.bind fun x => (uniformOfFintype T).map (f x)) ^ 2 -
        winProb (X.bind fun x => (uniformOfFintype T).map (f x)) / Fintype.card T ≤
      winProb (X.bind fun x => (uniformOfFintype T).bind fun y =>
        (uniformOfFintype T).map fun y' => f x y && f x y' && decide (y ≠ y')) := by
  set N : ℝ := (Fintype.card T : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  -- `g x` is the success probability of one run on `x`.
  set g : S → ℝ := fun x => winProb ((uniformOfFintype T).map (f x))
  have hg0 : ∀ x, 0 ≤ g x := fun x => winProb_nonneg _
  have hg1 : ∀ x, g x ≤ 1 := fun x => winProb_le_one _
  -- Two runs on `x` with distinct challenges succeed with probability `g x ^ 2 - g x / N`.
  have hpair : ∀ x, winProb ((uniformOfFintype T).bind fun y =>
      (uniformOfFintype T).map fun y' => f x y && f x y' && decide (y ≠ y')) =
        g x ^ 2 - g x / N := by
    intro x
    set A := univ.filter fun t => f x t = true
    have hA : g x = A.card / N := winProb_map_uniform (f x)
    have hprod : ((uniformOfFintype T).bind fun y =>
        (uniformOfFintype T).map fun y' => f x y && f x y' && decide (y ≠ y')) =
          (uniformOfFintype (T × T)).map fun p => f x p.1 && f x p.2 && decide (p.1 ≠ p.2) := by
      rw [← uniformOfFintype_prod T T, PMF.map_bind]
      simp_rw [PMF.map_comp]
      rfl
    have hfilter : (univ.filter fun p : T × T =>
        (f x p.1 && f x p.2 && decide (p.1 ≠ p.2)) = true) = A.offDiag := by
      ext p
      simp [A, mem_offDiag, and_assoc]
    rw [hprod, winProb_map_uniform, hfilter, offDiag_card, Fintype.card_prod, hA,
      Nat.cast_sub (Nat.le_mul_self _)]
    push_cast
    field_simp
    ring
  rw [winProb_bind, winProb_bind]
  simp_rw [hpair]
  -- Averaging over `X`: Jensen's inequality for the square of `g`.
  have hw : Summable fun x => (X x).toReal := ENNReal.summable_toReal (by simp [X.tsum_coe])
  have hone : ∑' x, (X x).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq fun x => X.apply_ne_top x, X.tsum_coe, ENNReal.toReal_one]
  have hs1 : Summable fun x => (X x).toReal * g x :=
    hw.of_nonneg_of_le (fun x => mul_nonneg ENNReal.toReal_nonneg (hg0 x))
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (hg1 x))
  have hs2 : Summable fun x => (X x).toReal * g x ^ 2 :=
    hw.of_nonneg_of_le (fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ (hg0 x) (hg1 x)))
  set m := ∑' x, (X x).toReal * g x
  have hvar : ∑' x, (X x).toReal * (g x - m) ^ 2 = ∑' x, (X x).toReal * g x ^ 2 - m ^ 2 := by
    calc ∑' x, (X x).toReal * (g x - m) ^ 2
        = ∑' x, ((X x).toReal * g x ^ 2 - 2 * m * ((X x).toReal * g x) +
            m ^ 2 * (X x).toReal) := tsum_congr fun x => by ring
      _ = ∑' x, (X x).toReal * g x ^ 2 - m ^ 2 := by
        rw [(hs2.sub (hs1.mul_left _)).tsum_add (hw.mul_left _), hs2.tsum_sub (hs1.mul_left _),
          tsum_mul_left, tsum_mul_left, hone]
        ring
  have hnonneg : 0 ≤ ∑' x, (X x).toReal * (g x - m) ^ 2 :=
    tsum_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hrhs : ∑' x, (X x).toReal * (g x ^ 2 - g x / N) = ∑' x, (X x).toReal * g x ^ 2 - m / N := by
    calc ∑' x, (X x).toReal * (g x ^ 2 - g x / N)
        = ∑' x, ((X x).toReal * g x ^ 2 - N⁻¹ * ((X x).toReal * g x)) :=
          tsum_congr fun x => by ring
      _ = ∑' x, (X x).toReal * g x ^ 2 - m / N := by
        rw [hs2.tsum_sub (hs1.mul_left _), tsum_mul_left, inv_mul_eq_div]
  rw [hrhs]
  linarith

end Cslib.Crypto.Framework
