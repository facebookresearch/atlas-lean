/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicLocalBallot
import Code.Universality.IsingFermionicFourthMoment









namespace StatMech.Universality

open Finset

noncomputable section

private def EndpointFirstBoundaryExtension (m K : Nat) :=
  Σ j : Fin (K + 1),
    IsingLineFirstBoundaryFamily m j ×
      {tail : List Bool // tail.length = K - j}

private theorem isingLineChoiceRun_append_endpointRace
    (n : Nat) (p : IsingLineBox n) (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

private theorem isingLineChoiceRun_of_boundary_endpointRace
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun]
      rw [show isingLineChoiceNext n p b = p by
        simp [isingLineChoiceNext, hp]]
      exact ih

private def endpointFirstBoundaryExtend (m K : Nat) :
    EndpointFirstBoundaryExtension m K →
      {ys : List Bool // ys.length = K ∧
        isingLineBoxBoundary (2 * m)
          (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)} := fun w =>
  ⟨w.2.1.1 ++ w.2.2.1, by
      rw [List.length_append, w.2.1.2.1, w.2.2.2]
      omega,
    by
      rw [isingLineChoiceRun_append_endpointRace]
      rw [isingLineChoiceRun_of_boundary_endpointRace
        (2 * m) _ w.2.1.2.2.1]
      exact w.2.1.2.2.1⟩

private theorem endpointFirstBoundaryExtend_injective (m K : Nat) :
    Function.Injective (endpointFirstBoundaryExtend m K) := by
  rintro ⟨aj, ap, atail⟩ ⟨bj, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hj : (aj : Nat) = bj := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (aj : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
      change (ap.1 ++ atail.1).take (aj : Nat) =
        (bp.1 ++ btail.1).take (aj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (aj : Nat) = ap.1 := by
        simpa [ap.2.1] using
          (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (aj : Nat) =
          bp.1.take (aj : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      rw [haTake, hbTake] at ht
      rw [← ht]
      exact ap.2.2.1
    · have haavoid := ap.2.2.2 (bj : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (bj : Nat)) hfull
      change (ap.1 ++ atail.1).take (bj : Nat) =
        (bp.1 ++ btail.1).take (bj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (bj : Nat) =
          ap.1.take (bj : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (bj : Nat) = bp.1 := by
        simpa [bp.2.1] using
          (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      rw [haTake, hbTake] at ht
      rw [ht]
      exact bp.2.2.1
  have hjSubtype : aj = bj := Fin.ext hj
  subst bj
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  have hat : atail = btail := Subtype.ext htail
  subst bp
  subst btail
  rfl

private def EndpointBoundaryStringFamily (m K : Nat) :=
  {ys : List Bool // ys.length = K ∧
    isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)}

noncomputable instance endpointBoundaryStringFamily_finite (m K : Nat) :
    Finite (EndpointBoundaryStringFamily m K) := by
  letI : Fintype {ys : List Bool // ys.length = K} :=
    (List.finite_length_eq Bool K).fintype
  exact Finite.of_injective
    (fun w : EndpointBoundaryStringFamily m K =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = K}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = K} => z.1) h)

private def endpointBoundaryStringToSum (m K : Nat) (hm : 0 < m) :
    EndpointBoundaryStringFamily m K →
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := fun w => by
  by_cases hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
  · exact Sum.inl ⟨w.1, w.2.1, Fin.ext hzero⟩
  · exact Sum.inr ⟨w.1, w.2.1, Fin.ext (by
      have hb := w.2.2
      unfold isingLineBoxBoundary at hb
      rcases hb with h | h
      · exact (hzero h).elim
      · exact h)⟩

private def endpointBoundarySumToString (m K : Nat) :
    IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ →
      EndpointBoundaryStringFamily m K
  | Sum.inl w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      left
      simpa [w.2.2]⟩
  | Sum.inr w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      right
      simpa [w.2.2]⟩

private def endpointBoundaryStringEquivSum
    (m K : Nat) (hm : 0 < m) :
    EndpointBoundaryStringFamily m K ≃
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ where
  toFun := endpointBoundaryStringToSum m K hm
  invFun := endpointBoundarySumToString m K
  left_inv w := by
    unfold endpointBoundaryStringToSum
    by_cases hzero :
        (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
    · rw [dif_pos hzero]
      rfl
    · rw [dif_neg hzero]
      rfl
  right_inv w := by
    cases w with
    | inl w =>
        unfold endpointBoundarySumToString endpointBoundaryStringToSum
        have hzero :
            (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0 := by
          simp [w.2.2]
        rw [dif_pos hzero]
        apply congrArg Sum.inl
        exact Subtype.ext rfl
    | inr w =>
        unfold endpointBoundarySumToString endpointBoundaryStringToSum
        have hne :
            (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 ≠ 0 := by
          simp [w.2.2]
          omega
        rw [dif_neg hne]
        apply congrArg Sum.inr
        exact Subtype.ext rfl

private theorem lineFirstBoundary_partial_weight_le_stopped
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤
      isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := by
  have hcard : Nat.card (EndpointFirstBoundaryExtension m K) ≤
      Nat.card (EndpointBoundaryStringFamily m K) :=
    Nat.card_le_card_of_injective (endpointFirstBoundaryExtend m K)
      (endpointFirstBoundaryExtend_injective m K)
  have hext : Nat.card (EndpointFirstBoundaryExtension m K) =
      ∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j) := by
    letI (j : Fin (K + 1)) :
        Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (K + 1)) :
        Fintype {tail : List Bool // tail.length = K - j} :=
      (List.finite_length_eq Bool (K - j)).fintype
    change Nat.card (Σ j : Fin (K + 1),
      IsingLineFirstBoundaryFamily m j ×
        {tail : List Bool // tail.length = K - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (K - (j : Nat))) = 2 ^ (K - (j : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (K - (j : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hboundary : Nat.card (EndpointBoundaryStringFamily m K) =
      Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨0, by omega⟩) +
        Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨2 * m, by omega⟩) := by
    rw [Nat.card_congr (endpointBoundaryStringEquivSum m K hm), Nat.card_sum]
  have hweightedNat :
      (∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j)) ≤
          Nat.card (EndpointBoundaryStringFamily m K) := by
    rw [← hext]
    exact hcard
  have hweightedReal :
      (∑ j : Fin (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) ≤
          (Nat.card (EndpointBoundaryStringFamily m K) : Real) := by
    exact_mod_cast hweightedNat
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
      (2 : Real) ^ (K - j)) (K + 1)] at hweightedReal
  have htwo : 0 < (2 : Real) ^ K := by positivity
  have hdiv := div_le_div_of_nonneg_right hweightedReal htwo.le
  calc
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) =
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := by
        have := Finset.mem_range.mp hj
        omega
      have hpow : (2 : Real) ^ K =
          (2 : Real) ^ j * (2 : Real) ^ (K - j) := by
        calc
          (2 : Real) ^ K = (2 : Real) ^ (j + (K - j)) := by
            congr 1
            omega
          _ = _ := pow_add _ _ _
      calc
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
            (2 : Real) ^ j =
          ((Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
            (2 : Real) ^ (K - j)) /
              ((2 : Real) ^ j * (2 : Real) ^ (K - j)) :=
            (mul_div_mul_right _ _ (by positivity)).symm
        _ = _ := by rw [hpow]
    _ ≤ (Nat.card (EndpointBoundaryStringFamily m K) : Real) /
        (2 : Real) ^ K := hdiv
    _ = isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := by
      rw [hboundary]
      push_cast
      rw [add_div]
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div,
        isingLineStoppedKernel_eq_natCard_choicePath_div]


theorem lineFirstBoundary_partial_weight_le_fourth
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤
      3 * (K : Real) ^ 2 / (m : Real) ^ 4 :=
  (lineFirstBoundary_partial_weight_le_stopped m K hm).trans
    (isingLineStoppedKernel_center_boundary_le_fourth m K hm)

theorem endpointRace_sum_mul_eq_last_partial_add
    (a b : Nat → Real) (N : Nat) :
    (∑ k ∈ Finset.range (N + 1), a k * b k) =
      a N * (∑ k ∈ Finset.range (N + 1), b k) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) *
            (∑ j ∈ Finset.range (k + 1), b j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (N + 1 + 1), a k * b k) =
            (∑ k ∈ Finset.range (N + 1), a k * b k) +
              a (N + 1) * b (N + 1) := by rw [Finset.sum_range_succ]
        _ = (a N * (∑ k ∈ Finset.range (N + 1), b k) +
              ∑ k ∈ Finset.range N,
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j)) +
              a (N + 1) * b (N + 1) := by rw [ih]
        _ = a (N + 1) * (∑ k ∈ Finset.range (N + 1 + 1), b k) +
              ∑ k ∈ Finset.range (N + 1),
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j) := by
            have hbSucc : (∑ k ∈ Finset.range (N + 1 + 1), b k) =
                (∑ k ∈ Finset.range (N + 1), b k) + b (N + 1) := by
              rw [Finset.sum_range_succ]
            have hdSucc :
                (∑ k ∈ Finset.range (N + 1),
                  (a k - a (k + 1)) *
                    (∑ j ∈ Finset.range (k + 1), b j)) =
                  (∑ k ∈ Finset.range N,
                    (a k - a (k + 1)) *
                      (∑ j ∈ Finset.range (k + 1), b j)) +
                    (a N - a (N + 1)) *
                      (∑ j ∈ Finset.range (N + 1), b j) := by
              rw [Finset.sum_range_succ]
            rw [hbSucc, hdSucc]
            ring



theorem endpointBallot_firstBoundary_sum_le
    (m N : Nat) (hm : 0 < m) (hN : N ≤ m * m) :
    (∑ k ∈ Finset.range (N + 1),
      (4 / (k + 1 : Real)) *
        ((Nat.card (IsingLineFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) ≤
      24 / (m : Real) ^ 2 := by
  let a : Nat → Real := fun k => 4 / (k + 1 : Real)
  let b : Nat → Real := fun k =>
    (Nat.card (IsingLineFirstBoundaryFamily m k) : Real) / (2 : Real) ^ k
  have hm2 : 0 < (m : Real) ^ 2 := by positivity
  have hm4 : 0 < (m : Real) ^ 4 := by positivity
  have hNReal : (N : Real) ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show N ≤ m ^ 2 by simpa [pow_two] using hN)
  have hpartial (k : Nat) :
      (∑ j ∈ Finset.range (k + 1), b j) ≤
        3 * (k : Real) ^ 2 / (m : Real) ^ 4 := by
    simpa [b] using lineFirstBoundary_partial_weight_le_fourth m k hm
  have hlast :
      a N * (∑ k ∈ Finset.range (N + 1), b k) ≤
        12 / (m : Real) ^ 2 := by
    calc
      _ ≤ a N * (3 * (N : Real) ^ 2 / (m : Real) ^ 4) := by
        apply mul_le_mul_of_nonneg_left (hpartial N)
        dsimp [a]
        positivity
      _ ≤ 12 / (m : Real) ^ 2 := by
        dsimp [a]
        have hN1 : (0 : Real) < N + 1 := by positivity
        have hN2 : (N : Real) ^ 2 ≤
            (N + 1 : Real) * (m : Real) ^ 2 := by
          have hmul := mul_le_mul hNReal
            (show (N : Real) ≤ N + 1 by norm_num)
            (by positivity) (by positivity)
          nlinarith
        have hN2mul := mul_le_mul_of_nonneg_right hN2 hm2.le
        calc
          4 / (N + 1 : Real) *
                (3 * (N : Real) ^ 2 / (m : Real) ^ 4) =
              12 * (N : Real) ^ 2 /
                ((N + 1 : Real) * (m : Real) ^ 4) := by
            field_simp
            ring
          _ ≤ 12 / (m : Real) ^ 2 := by
            rw [div_le_div_iff₀ (mul_pos hN1 hm4) hm2]
            have hmul12 := mul_le_mul_of_nonneg_left hN2mul
              (show (0 : Real) ≤ 12 by norm_num)
            convert hmul12 using 1 <;> ring
  have hterm (k : Nat) :
      (a k - a (k + 1)) *
          (∑ j ∈ Finset.range (k + 1), b j) ≤
        12 / (m : Real) ^ 4 := by
    have hdiff : 0 ≤ a k - a (k + 1) := by
      dsimp [a]
      have hk1 : (0 : Real) < k + 1 := by positivity
      have hk2 : (0 : Real) < k + 2 := by positivity
      apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_left (by norm_num) hk1 (by norm_num)
    calc
      _ ≤ (a k - a (k + 1)) *
          (3 * (k : Real) ^ 2 / (m : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left (hpartial k) hdiff
      _ ≤ 12 / (m : Real) ^ 4 := by
        dsimp [a]
        norm_num [Nat.cast_add, Nat.cast_one]
        have hk1 : (0 : Real) < k + 1 := by positivity
        have hk2 : (0 : Real) < (k : Real) + 1 + 1 := by positivity
        have hkSq : (k : Real) ^ 2 ≤
            ((k : Real) + 1) * ((k : Real) + 1 + 1) := by
          nlinarith [show (0 : Real) ≤ k by positivity]
        have hkSqMul := mul_le_mul_of_nonneg_right hkSq hm4.le
        calc
          (4 / ((k : Real) + 1) - 4 / ((k : Real) + 1 + 1)) *
                (3 * (k : Real) ^ 2 / (m : Real) ^ 4) =
              12 * (k : Real) ^ 2 /
                ((((k : Real) + 1) * ((k : Real) + 1 + 1)) *
                  (m : Real) ^ 4) := by
            field_simp
            ring
          _ ≤ 12 / (m : Real) ^ 4 := by
            rw [div_le_div_iff₀ (mul_pos (mul_pos hk1 hk2) hm4) hm4]
            have hmul12 := mul_le_mul_of_nonneg_left hkSqMul
              (show (0 : Real) ≤ 12 by norm_num)
            convert hmul12 using 1 <;> ring
  rw [show (∑ k ∈ Finset.range (N + 1),
      (4 / (k + 1 : Real)) *
        ((Nat.card (IsingLineFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) =
      ∑ k ∈ Finset.range (N + 1), a k * b k by rfl]
  rw [endpointRace_sum_mul_eq_last_partial_add]
  calc
    _ ≤ 12 / (m : Real) ^ 2 +
        ∑ k ∈ Finset.range N, 12 / (m : Real) ^ 4 := by
      exact add_le_add hlast (Finset.sum_le_sum fun k hk => hterm k)
    _ = 12 / (m : Real) ^ 2 +
        (N : Real) * (12 / (m : Real) ^ 4) := by
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul]
    _ ≤ 12 / (m : Real) ^ 2 + 12 / (m : Real) ^ 2 := by
      apply add_le_add (le_refl _)
      calc
        (N : Real) * (12 / (m : Real) ^ 4) ≤
            (m : Real) ^ 2 * (12 / (m : Real) ^ 4) :=
          mul_le_mul_of_nonneg_right hNReal (by positivity)
        _ = 12 / (m : Real) ^ 2 := by field_simp
    _ = 24 / (m : Real) ^ 2 := by ring



def IsingEndpointTransverseRaceWitnessFamily
    (m t : Nat) (level target : Int) :=
  Σ j : Fin (t + 1),
    IsingHorizontalNoHitEndpointFamily j level target ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j}

noncomputable instance isingEndpointTransverseRaceWitnessFamily_finite
    (m t : Nat) (level target : Int) :
    Finite (IsingEndpointTransverseRaceWitnessFamily m t level target) := by
  letI (j : Fin (t + 1)) :
      Fintype (IsingHorizontalNoHitEndpointFamily j level target) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  change Finite (Σ j : Fin (t + 1),
    IsingHorizontalNoHitEndpointFamily j level target ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j})
  infer_instance


theorem endpointTransverseRaceWitness_weight_le
    (m t : Nat) (level target : Int) (hm : 0 < m) (ht : t ≤ m * m) :
    Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) /
        (4 : Real) ^ t ≤
      24 / (m : Real) ^ 2 := by
  have hcard :
      Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) =
        ∑ j : Fin (t + 1),
          Nat.card (IsingHorizontalNoHitEndpointFamily j level target) *
            Nat.card (IsingLineFirstBoundaryFamily m j) * 4 ^ (t - j) := by
    letI (j : Fin (t + 1)) :
        Fintype (IsingHorizontalNoHitEndpointFamily j level target) :=
      Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
      (List.finite_length_eq (Bool × Bool) (t - j)).fintype
    change Nat.card (Σ j : Fin (t + 1),
      IsingHorizontalNoHitEndpointFamily j level target ×
        IsingLineFirstBoundaryFamily m j ×
          {tail : List (Bool × Bool) // tail.length = t - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    have htail : Nat.card
        {tail : List (Bool × Bool) // tail.length = t - (j : Nat)} =
        4 ^ (t - (j : Nat)) := by
      change Nat.card (List.Vector (Bool × Bool) (t - (j : Nat))) =
        4 ^ (t - (j : Nat))
      rw [Nat.card_congr
          (Equiv.vectorEquivFin (Bool × Bool) (t - (j : Nat))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num
    calc
      Nat.card (IsingHorizontalNoHitEndpointFamily j level target ×
          IsingLineFirstBoundaryFamily m j ×
            {tail : List (Bool × Bool) // tail.length = t - j}) =
        Nat.card (IsingHorizontalNoHitEndpointFamily j level target) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) *
            Nat.card {tail : List (Bool × Bool) // tail.length = t - j}) := by
          rw [Nat.card_prod, Nat.card_prod]
      _ = _ := by rw [htail]; ring
  have hmass :
      Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) /
          (4 : Real) ^ t =
        ∑ j ∈ Finset.range (t + 1),
          (Nat.card (IsingHorizontalNoHitEndpointFamily j level target) /
              (2 : Real) ^ j) *
            (Nat.card (IsingLineFirstBoundaryFamily m j) /
              (2 : Real) ^ j) := by
    rw [hcard]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat =>
        (Nat.card (IsingHorizontalNoHitEndpointFamily j level target) : Real) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
            (4 : Real) ^ (t - j)) (t + 1)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j ≤ t := by
      have := Finset.mem_range.mp hj
      omega
    have hfour : (4 : Real) ^ t =
        (4 : Real) ^ j * (4 : Real) ^ (t - j) := by
      calc
        (4 : Real) ^ t = (4 : Real) ^ (j + (t - j)) := by
          congr 1
          omega
        _ = _ := pow_add _ _ _
    have htwo : (4 : Real) ^ j =
        (2 : Real) ^ j * (2 : Real) ^ j := by
      rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
    rw [hfour, htwo]
    field_simp
  rw [hmass]
  calc
    _ ≤ ∑ j ∈ Finset.range (t + 1),
        (4 / (j + 1 : Real)) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) /
            (2 : Real) ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right
        (horizontalNoHitEndpoint_weight_le j level target)
      positivity
    _ ≤ 24 / (m : Real) ^ 2 :=
      endpointBallot_firstBoundary_sum_le m t hm ht



theorem endpointTransverseRaceWitness_diffusive_weight_le
    (rho m : Nat) (level target : Int) (hρ : 0 < rho) (hm : rho ≤ m) :
    Nat.card (IsingEndpointTransverseRaceWitnessFamily
          m (rho * rho) level target) /
        (4 : Real) ^ (rho * rho) ≤
      24 / (rho : Real) ^ 2 := by
  have hm0 : 0 < m := lt_of_lt_of_le hρ hm
  have ht : rho * rho ≤ m * m := Nat.mul_self_le_mul_self hm
  have h := endpointTransverseRaceWitness_weight_le
    m (rho * rho) level target hm0 ht
  have hrm : (rho : Real) ^ 2 ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 ≤ m ^ 2 by
      simpa [pow_two] using ht)
  calc
    _ ≤ 24 / (m : Real) ^ 2 := h
    _ ≤ 24 / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hrm

end

end StatMech.Universality
