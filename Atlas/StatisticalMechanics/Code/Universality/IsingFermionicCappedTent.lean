/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicProductGreenBarrier










namespace StatMech.Universality

noncomputable section


def isingNatCappedTent (source i : Nat) : Real :=
  (Nat.min i source : Nat)


noncomputable def isingNatCappedRobinTent
    (coefficient : Real) (source i : Nat) : Real :=
  isingNatCappedTent source i + 1 / coefficient


def isingNatReverseCappedTent (top source i : Nat) : Real :=
  isingNatCappedTent (top - source) (top - i)

theorem isingNatCappedTent_nonneg (source i : Nat) :
    0 <= isingNatCappedTent source i := by
  unfold isingNatCappedTent
  positivity

theorem isingNatCappedTent_le_coordinate (source i : Nat) :
    isingNatCappedTent source i <= (i : Real) := by
  unfold isingNatCappedTent
  exact_mod_cast Nat.min_le_left i source

theorem isingNatCappedTent_self (source : Nat) :
    isingNatCappedTent source source = (source : Real) := by
  simp [isingNatCappedTent]

theorem isingNatCappedRobinTent_nonneg
    (coefficient : Real) (hcoefficient : 0 < coefficient)
    (source i : Nat) :
    0 <= isingNatCappedRobinTent coefficient source i := by
  exact add_nonneg (isingNatCappedTent_nonneg source i)
    (one_div_nonneg.mpr hcoefficient.le)


theorem isingNatCappedTent_secondDifference_nonpos
    (source i : Nat) (hi : 0 < i) :
    isingNatCappedTent source (i + 1) +
        isingNatCappedTent source (i - 1) -
          2 * isingNatCappedTent source i <= 0 := by
  unfold isingNatCappedTent
  by_cases his : i < source
  · have hi1 : i + 1 <= source := by omega
    have him1 : i - 1 <= source := (Nat.sub_le i 1).trans (Nat.le_of_lt his)
    simp only [Nat.min_eq_left hi1, Nat.min_eq_left him1,
      Nat.min_eq_left (Nat.le_of_lt his)]
    push_cast
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hi))]
    ring_nf
    exact le_rfl
  · by_cases hsi : source < i
    · have hs1 : source <= i - 1 := by omega
      have hsip1 : source <= i + 1 := by omega
      simp only [Nat.min_eq_right hsip1,
        Nat.min_eq_right hs1, Nat.min_eq_right (Nat.le_of_lt hsi)]
      ring_nf
      exact le_rfl
    · have hieq : i = source := by omega
      subst i
      have hsip1 : source <= source + 1 := by omega
      simp only [Nat.min_eq_right hsip1,
        Nat.min_eq_left (Nat.sub_le source 1), Nat.min_self]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hi))]
      linarith


theorem isingNatCappedTent_secondDifference_source
    (source : Nat) (hsource : 0 < source) :
    isingNatCappedTent source (source + 1) +
        isingNatCappedTent source (source - 1) -
          2 * isingNatCappedTent source source = -1 := by
  unfold isingNatCappedTent
  have hsip1 : source <= source + 1 := by omega
  simp only [Nat.min_eq_right hsip1,
    Nat.min_eq_left (Nat.sub_le source 1), Nat.min_self]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hsource))]
  ring

theorem isingNatCappedRobinTent_secondDifference_nonpos
    (coefficient : Real) (source i : Nat) (hi : 0 < i) :
    isingNatCappedRobinTent coefficient source (i + 1) +
        isingNatCappedRobinTent coefficient source (i - 1) -
          2 * isingNatCappedRobinTent coefficient source i <= 0 := by
  unfold isingNatCappedRobinTent
  have h := isingNatCappedTent_secondDifference_nonpos source i hi
  linarith

theorem isingNatCappedRobinTent_secondDifference_source
    (coefficient : Real) (source : Nat) (hsource : 0 < source) :
    isingNatCappedRobinTent coefficient source (source + 1) +
        isingNatCappedRobinTent coefficient source (source - 1) -
          2 * isingNatCappedRobinTent coefficient source source = -1 := by
  unfold isingNatCappedRobinTent
  have h := isingNatCappedTent_secondDifference_source source hsource
  linarith



theorem isingNatCappedRobinTent_left_balance
    (coefficient : Real) (hcoefficient : 0 < coefficient)
    (source : Nat) (hsource : 0 < source) :
    isingNatCappedRobinTent coefficient source 1 -
        isingNatCappedRobinTent coefficient source 0 -
          coefficient * isingNatCappedRobinTent coefficient source 0 = 0 := by
  unfold isingNatCappedRobinTent isingNatCappedTent
  have hs : 1 <= source := hsource
  simp only [Nat.min_eq_left hs,
    Nat.min_eq_left (Nat.zero_le source), Nat.cast_one, Nat.cast_zero]
  field_simp [hcoefficient.ne']
  ring



theorem isingNatCappedTent_predecessor_sub_nonpos
    (source i : Nat) :
    isingNatCappedTent source (i - 1) -
      isingNatCappedTent source i <= 0 := by
  unfold isingNatCappedTent
  have h : Nat.min (i - 1) source <= Nat.min i source := by
    simp only [Nat.min_def]
    split <;> split <;> omega
  have hreal : ((Nat.min (i - 1) source : Nat) : Real) <=
      (Nat.min i source : Nat) := by
    exact_mod_cast h
  linarith

theorem isingNatCappedRobinTent_predecessor_sub_nonpos
    (coefficient : Real) (source i : Nat) :
    isingNatCappedRobinTent coefficient source (i - 1) -
      isingNatCappedRobinTent coefficient source i <= 0 := by
  unfold isingNatCappedRobinTent
  have h := isingNatCappedTent_predecessor_sub_nonpos source i
  linarith

theorem isingNatReverseCappedTent_nonneg (top source i : Nat) :
    0 <= isingNatReverseCappedTent top source i :=
  isingNatCappedTent_nonneg (top - source) (top - i)

theorem isingNatReverseCappedTent_le_coordinate
    (top source i : Nat) :
    isingNatReverseCappedTent top source i <= (top - i : Nat) := by
  exact isingNatCappedTent_le_coordinate (top - source) (top - i)

theorem isingNatReverseCappedTent_self
    (top source : Nat) :
    isingNatReverseCappedTent top source source = (top - source : Nat) := by
  simp [isingNatReverseCappedTent, isingNatCappedTent_self]

theorem isingNatReverseCappedTent_secondDifference_nonpos
    (top source i : Nat) (hi : 0 < i) (hitop : i < top) :
    isingNatReverseCappedTent top source (i + 1) +
        isingNatReverseCappedTent top source (i - 1) -
          2 * isingNatReverseCappedTent top source i <= 0 := by
  have hnext : top - (i + 1) = top - i - 1 := by omega
  have hprev : top - (i - 1) = top - i + 1 := by omega
  unfold isingNatReverseCappedTent
  rw [hnext, hprev]
  have h := isingNatCappedTent_secondDifference_nonpos
    (top - source) (top - i) (by omega)
  linarith

theorem isingNatReverseCappedTent_secondDifference_source
    (top source : Nat) (hsource : 0 < source) (hsourceTop : source < top) :
    isingNatReverseCappedTent top source (source + 1) +
        isingNatReverseCappedTent top source (source - 1) -
          2 * isingNatReverseCappedTent top source source = -1 := by
  have hnext : top - (source + 1) = top - source - 1 := by omega
  have hprev : top - (source - 1) = top - source + 1 := by omega
  unfold isingNatReverseCappedTent
  rw [hnext, hprev]
  have h := isingNatCappedTent_secondDifference_source
    (top - source) (by omega)
  linarith

end

end StatMech.Universality
