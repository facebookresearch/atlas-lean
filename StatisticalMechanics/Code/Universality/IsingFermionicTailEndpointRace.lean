/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointRace





namespace StatMech.Universality

open Finset

noncomputable section


abbrev IsingEndpointRaceTail (t : Nat) (j : Fin (t + 1)) :=
  {tail : List (Bool × Bool) // tail.length = t - j}



def IsingTailDependentEndpointRaceFamily
    (m t : Nat) (level : Int)
    (target : (j : Fin (t + 1)) ->
      IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail t j -> Int) :=
  Σ j : Fin (t + 1),
    Σ pref : IsingLineFirstBoundaryFamily m j,
      Σ tail : IsingEndpointRaceTail t j,
        IsingHorizontalNoHitEndpointFamily j level (target j pref tail)

noncomputable instance isingTailDependentEndpointRaceFamily_finite
    (m t : Nat) (level : Int)
    (target : (j : Fin (t + 1)) ->
      IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail t j -> Int) :
    Finite (IsingTailDependentEndpointRaceFamily m t level target) := by
  letI (j : Fin (t + 1)) : Fintype (IsingLineFirstBoundaryFamily m j) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) : Fintype (IsingEndpointRaceTail t j) :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  letI (j : Fin (t + 1))
      (pref : IsingLineFirstBoundaryFamily m j)
      (tail : IsingEndpointRaceTail t j) :
      Fintype (IsingHorizontalNoHitEndpointFamily
        j level (target j pref tail)) :=
    Fintype.ofFinite _
  unfold IsingTailDependentEndpointRaceFamily
  infer_instance



theorem tailDependentEndpointRace_weight_le
    (m t : Nat) (level : Int)
    (target : (j : Fin (t + 1)) ->
      IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail t j -> Int)
    (hm : 0 < m) (ht : t <= m * m) :
    Nat.card (IsingTailDependentEndpointRaceFamily m t level target) /
        (4 : Real) ^ t <=
      24 / (m : Real) ^ 2 := by
  letI (j : Fin (t + 1)) : Fintype (IsingLineFirstBoundaryFamily m j) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) : Fintype (IsingEndpointRaceTail t j) :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  letI (j : Fin (t + 1))
      (pref : IsingLineFirstBoundaryFamily m j)
      (tail : IsingEndpointRaceTail t j) :
      Fintype (IsingHorizontalNoHitEndpointFamily
        j level (target j pref tail)) :=
    Fintype.ofFinite _
  have hcard :
      Nat.card (IsingTailDependentEndpointRaceFamily m t level target) =
        ∑ j : Fin (t + 1),
          ∑ pref : IsingLineFirstBoundaryFamily m j,
            ∑ tail : IsingEndpointRaceTail t j,
              Nat.card (IsingHorizontalNoHitEndpointFamily
                j level (target j pref tail)) := by
    unfold IsingTailDependentEndpointRaceFamily
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro pref hpref
    rw [Nat.card_sigma]
  rw [hcard]
  push_cast
  rw [Finset.sum_div]
  calc
    _ <= ∑ j : Fin (t + 1),
        (4 / ((j : Nat) + 1 : Real)) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) /
            (2 : Real) ^ (j : Nat)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjt : (j : Nat) <= t := Nat.le_of_lt_succ j.isLt
      have htailCard : Nat.card (IsingEndpointRaceTail t j) =
          4 ^ (t - (j : Nat)) := by
        change Nat.card (List.Vector (Bool × Bool) (t - (j : Nat))) =
          4 ^ (t - (j : Nat))
        rw [Nat.card_congr
            (Equiv.vectorEquivFin (Bool × Bool) (t - (j : Nat))),
          Nat.card_eq_fintype_card, Fintype.card_fun]
        norm_num
      have hno (pref : IsingLineFirstBoundaryFamily m j)
          (tail : IsingEndpointRaceTail t j) :
          (Nat.card (IsingHorizontalNoHitEndpointFamily
              j level (target j pref tail)) : Real) <=
            (4 / ((j : Nat) + 1 : Real)) * (2 : Real) ^ (j : Nat) := by
        have h := horizontalNoHitEndpoint_weight_le
          j level (target j pref tail)
        have hp : 0 < (2 : Real) ^ (j : Nat) := by positivity
        exact (div_le_iff₀ hp).mp h
      have htailSum (pref : IsingLineFirstBoundaryFamily m j) :
          (∑ tail : IsingEndpointRaceTail t j,
              (Nat.card (IsingHorizontalNoHitEndpointFamily
                j level (target j pref tail)) : Real)) <=
            (4 : Real) ^ (t - (j : Nat)) *
              ((4 / ((j : Nat) + 1 : Real)) *
                (2 : Real) ^ (j : Nat)) := by
        calc
          _ <= ∑ _tail : IsingEndpointRaceTail t j,
                (4 / ((j : Nat) + 1 : Real)) *
                  (2 : Real) ^ (j : Nat) :=
            Finset.sum_le_sum fun tail _ => hno pref tail
          _ = (Nat.card (IsingEndpointRaceTail t j) : Real) *
                ((4 / ((j : Nat) + 1 : Real)) *
                  (2 : Real) ^ (j : Nat)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            congr 1
            norm_cast
            rw [Finset.card_univ, Nat.card_eq_fintype_card]
          _ = _ := by
            rw [htailCard]
            norm_cast
      have hprefSum :
          (∑ pref : IsingLineFirstBoundaryFamily m j,
              ∑ tail : IsingEndpointRaceTail t j,
                (Nat.card (IsingHorizontalNoHitEndpointFamily
                  j level (target j pref tail)) : Real)) <=
            (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
              ((4 : Real) ^ (t - (j : Nat)) *
                ((4 / ((j : Nat) + 1 : Real)) *
                  (2 : Real) ^ (j : Nat))) := by
        calc
          _ <= ∑ _pref : IsingLineFirstBoundaryFamily m j,
                (4 : Real) ^ (t - (j : Nat)) *
                  ((4 / ((j : Nat) + 1 : Real)) *
                    (2 : Real) ^ (j : Nat)) :=
            Finset.sum_le_sum fun pref _ => htailSum pref
          _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul]
            congr 1
            norm_cast
            rw [Finset.card_univ, Nat.card_eq_fintype_card]
      have hfour : (4 : Real) ^ t =
          (4 : Real) ^ (j : Nat) *
            (4 : Real) ^ (t - (j : Nat)) := by
        calc
          (4 : Real) ^ t =
              (4 : Real) ^ ((j : Nat) + (t - (j : Nat))) := by
            congr 1
            omega
          _ = _ := pow_add _ _ _
      have htwo : (4 : Real) ^ (j : Nat) =
          (2 : Real) ^ (j : Nat) * (2 : Real) ^ (j : Nat) := by
        rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
      calc
        (∑ pref : IsingLineFirstBoundaryFamily m j,
              ∑ tail : IsingEndpointRaceTail t j,
                (Nat.card (IsingHorizontalNoHitEndpointFamily
                  j level (target j pref tail)) : Real)) /
            (4 : Real) ^ t <=
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
              ((4 : Real) ^ (t - (j : Nat)) *
                ((4 / ((j : Nat) + 1 : Real)) *
                  (2 : Real) ^ (j : Nat))) /
            (4 : Real) ^ t := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact hprefSum
        _ = (4 / ((j : Nat) + 1 : Real)) *
            (Nat.card (IsingLineFirstBoundaryFamily m j) /
              (2 : Real) ^ (j : Nat)) := by
          rw [hfour, htwo]
          field_simp
    _ = ∑ j ∈ Finset.range (t + 1),
        (4 / (j + 1 : Real)) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) /
            (2 : Real) ^ j) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : Nat =>
          (4 / (j + 1 : Real)) *
            (Nat.card (IsingLineFirstBoundaryFamily m j) /
              (2 : Real) ^ j)) (t + 1)]
    _ <= 24 / (m : Real) ^ 2 :=
      endpointBallot_firstBoundary_sum_le m t hm ht


theorem tailDependentEndpointRace_diffusive_weight_le
    (rho m : Nat) (level : Int)
    (target : (j : Fin (rho * rho + 1)) ->
      IsingLineFirstBoundaryFamily m j ->
        IsingEndpointRaceTail (rho * rho) j -> Int)
    (hρ : 0 < rho) (hm : rho <= m) :
    Nat.card (IsingTailDependentEndpointRaceFamily
          m (rho * rho) level target) /
        (4 : Real) ^ (rho * rho) <=
      24 / (rho : Real) ^ 2 := by
  have hm0 : 0 < m := lt_of_lt_of_le hρ hm
  have ht : rho * rho <= m * m := Nat.mul_self_le_mul_self hm
  have h := tailDependentEndpointRace_weight_le
    m (rho * rho) level target hm0 ht
  have hrm : (rho : Real) ^ 2 <= (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 <= m ^ 2 by
      simpa [pow_two] using ht)
  exact h.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hrm)

end

end StatMech.Universality
