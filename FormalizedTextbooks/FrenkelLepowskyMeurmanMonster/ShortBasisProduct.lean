/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Products of short-vector basis elements in the concrete Conway algebra.
The actual Leech minimum supplies the short-output criterion, and sparse
contraction leaves the matrix outer product when the pairing is not ±16.
Source: Conway, Invent. Math. 79 (1985), §12, DOI: 10.1007/BF01388521.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortGeometry

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

theorem griessShortQ_product_base_class (r s u : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = (griessShortQ u).base ↔
      griessShortClass r + griessShortClass s = griessShortClass u := by
  constructor
  · intro h
    apply leechHyperbolicCoordinates.injective
    have hc := congrArg toAdd h
    change leechHyperbolicCoordinates (griessShortClass r) +
      leechHyperbolicCoordinates (griessShortClass s) =
        leechHyperbolicCoordinates (griessShortClass u) at hc
    simpa only [map_add] using hc
  · intro h
    apply Multiplicative.toAdd.injective
    change leechHyperbolicCoordinates (griessShortClass r) +
      leechHyperbolicCoordinates (griessShortClass s) =
        leechHyperbolicCoordinates (griessShortClass u)
    rw [← map_add, h]

theorem griessShortQ_product_base_one_iff (r s : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = 1 ↔ r = s := by
  constructor
  · intro h
    have hc := congrArg toAdd h
    change leechHyperbolicCoordinates (griessShortClass r) +
      leechHyperbolicCoordinates (griessShortClass s) = 0 at hc
    have hz : griessShortClass r + griessShortClass s = 0 := by
      apply leechHyperbolicCoordinates.injective
      simpa only [map_add, map_zero] using hc
    have hs : -griessShortClass s = griessShortClass s := by
      change -leechReduction (griessShortLatticeVector s) = leechReduction _
      rw [← map_neg, leechReduction_neg]
    apply griessShortClass_injective
    exact (add_eq_zero_iff_eq_neg.mp hz).trans hs
  · rintro rfl
    rw [griessShortQ_square]
    rfl

theorem griessShortQ_product_base_ne_short (r s : GriessShortIndex)
    (hplus : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) ≠ 16)
    (hminus : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) ≠ -16)
    (u : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base ≠ (griessShortQ u).base := by
  intro h
  have hc := (griessShortQ_product_base_class r s u).mp h
  have hs : IsLeechShortClass (griessShortClass r + griessShortClass s) := by
    rw [hc]
    exact (griessShortClassMap u).property
  rcases (griessShort_sum_class_iff_pairing r s).mp hs with h | h
  · exact hplus h
  · exact hminus h

noncomputable def conwayShortBasis (r : GriessShortIndex) : ConwayRawSpace :=
  (0, (Pi.single r 1, 0))

theorem finite_double_single_contraction {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (c : A → B → Prop) [DecidableRel c]
    (f : A → B → ℝ) (r : A) (s : B) :
    (∑ a, ∑ b, if c a b then f a b * (Pi.single r 1 : A → ℝ) a *
      (Pi.single s 1 : B → ℝ) b else 0) = if c r s then f r s else 0 := by
  calc
    _ = ∑ a, ∑ b, if a = r then if b = s then
        if c a b then f a b else 0 else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases ha : a = r <;> by_cases hb : b = s <;>
        simp [ha, hb]
    _ = _ := by
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]

theorem real_five_factor_reorder (a b c d e : ℝ) :
    a * b * c * d * e = a * d * e * b * c := by ring

set_option maxHeartbeats 500000 in
-- Bilinear contraction exposes the quotient extension fields in two finite sums.
set_option maxRecDepth 10000 in
-- The actual quotient action has several nested linear equivalences.
set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_shortBasis (r s : GriessShortIndex) :
    conwayRawProduct (conwayShortBasis r) (conwayShortBasis s) =
      ((fun i j => if (griessShortQ r * griessShortQ s).base = 1 then
        qSign (toAdd (griessShortQ r * griessShortQ s).coeff) *
          griessShortVector r i * griessShortVector r j else 0),
      ((fun u => if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
        qSign (toAdd (griessShortQ r * griessShortQ s).coeff) else 0), 0)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · funext i j
    dsimp only [conwayRawProduct, conwayShortBasis]
    simp only [Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero, add_zero, zero_add,
      Finset.sum_const_zero, zero_div]
    calc
      _ = ∑ a, ∑ b, if (griessShortQ a * griessShortQ b).base = 1 then
          (qSign (toAdd (griessShortQ a * griessShortQ b).coeff) *
            griessShortVector a i * griessShortVector a j) *
            (Pi.single r 1 : GriessShortIndex → ℝ) a *
            (Pi.single s 1 : GriessShortIndex → ℝ) b else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        split_ifs
        · exact real_five_factor_reorder _ _ _ _ _
        · rfl
      _ = _ := by
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single s]
          · simp only [Pi.single_apply, ite_true, mul_one]
          · intro b _ hb
            simp only [Pi.single_apply, ite_eq_right hb, mul_zero, ite_self]
          · simp
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          simp only [Pi.single_apply, ite_eq_right ha, mul_zero, zero_mul, ite_self]
        · simp
  · funext u
    dsimp only [conwayRawProduct, conwayShortBasis]
    simp only [Pi.zero_apply, zero_mul, mul_zero, add_zero,
      Finset.sum_const_zero, zero_div]
    simp only [conwayShortPairing, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single s]
      · simp only [Pi.single_apply, ite_true, mul_one]
      · intro b _ hb
        simp only [Pi.single_apply, ite_eq_right hb, mul_zero, ite_self]
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      simp only [Pi.single_apply, ite_eq_right ha, mul_zero, zero_mul, ite_self]
    · simp
  · funext t i
    dsimp only [conwayRawProduct, conwayShortBasis]
    simp only [Matrix.zero_apply, Pi.zero_apply, zero_mul, mul_zero, add_zero,
      Matrix.trace_zero, zero_div, Finset.sum_const_zero,
      show (fun _ : SpinIndex => (0 : ℝ)) = 0 from rfl, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_shortBasis_of_pairing (r s : GriessShortIndex)
    (hplus : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) ≠ 16)
    (hminus : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) ≠ -16) :
    conwayRawProduct (conwayShortBasis r) (conwayShortBasis s) =
      ((fun i j => if r = s then griessShortVector r i * griessShortVector r j else 0),
        (0, 0)) := by
  rw [conwayRawProduct_shortBasis]
  apply Prod.ext
  · funext i j
    by_cases h : r = s
    · subst s
      rw [griessShortQ_square]
      have hb : (1 : Q).base = 1 := rfl
      have hc : toAdd (1 : Q).coeff = 0 := rfl
      simp only [hb, hc, qSign_zero, ite_true, one_mul]
    · simp [griessShortQ_product_base_one_iff, h]
  · apply Prod.ext
    · funext u
      simp [griessShortQ_product_base_ne_short r s hplus hminus u]
    · rfl

theorem griessShortIntegral_self_pairing (r : GriessShortIndex) :
    leechIntegralPairing (griessShortIntegral r) (griessShortIntegral r) = 32 := by
  simpa only [leechIntegralPairing, leechSquareSum, pow_two] using
    griessShortIntegral_squareSum r

theorem conwayRawProduct_shortBasis_square (r : GriessShortIndex) :
    conwayRawProduct (conwayShortBasis r) (conwayShortBasis r) =
      ((fun i j => griessShortVector r i * griessShortVector r j), (0, 0)) := by
  have hp : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral r) ≠ 16 := by
    rw [griessShortIntegral_self_pairing]
    norm_num
  have hm : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral r) ≠ -16 := by
    rw [griessShortIntegral_self_pairing]
    norm_num
  simpa only [ite_true] using conwayRawProduct_shortBasis_of_pairing r r hp hm

theorem griessPairMinusPlus_pairing (p : Fin 276) :
    leechIntegralPairing (griessShortIntegral (Sum.inl (0, p)))
      (griessShortIntegral (Sum.inl (1, p))) = 0 := by
  have he (i : Fin 24) :
      griessShortIntegral (Sum.inl (0, p)) i * griessShortIntegral (Sum.inl (1, p)) i =
        16 * (if i = (griessCoordinatePair p).1 then 1 else 0) -
        16 * (if i = (griessCoordinatePair p).2 then 1 else 0) := by
    simp only [griessShortIntegral, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    split_ifs <;> norm_num
  change (∑ i, _) = 0
  simp_rw [he]
  simp [Finset.sum_sub_distrib]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
