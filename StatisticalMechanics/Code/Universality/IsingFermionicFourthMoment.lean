/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStoppedCoupling








open Finset

namespace StatMech.Universality

noncomputable section

private def isingLineCenteredFourth
    (m : Nat) (q : IsingLineBox (2 * m)) : Real :=
  ((q.1 : Real) - (m : Real)) ^ 4

private theorem isingLineCenteredFourth_step
    (m : Nat) (p : IsingLineBox (2 * m))
    (hp : ¬ isingLineBoxBoundary (2 * m) p) :
    isingLineCenteredFourth m (isingLineWest (2 * m) p) +
        isingLineCenteredFourth m (isingLineEast (2 * m) p hp) =
      2 * isingLineCenteredFourth m p +
        12 * ((p.1 : Real) - (m : Real)) ^ 2 + 2 := by
  unfold isingLineCenteredFourth isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < 2 * m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring



theorem isingLineStoppedMean_centeredFourth_le
    (m t : Nat) (p : IsingLineBox (2 * m)) :
    isingLineStoppedMean (2 * m) t (isingLineCenteredFourth m) p <=
      ((p.1 : Real) - (m : Real)) ^ 4 +
        6 * (t : Real) * ((p.1 : Real) - (m : Real)) ^ 2 +
          3 * (t : Real) ^ 2 := by
  induction t generalizing p with
  | zero =>
      simp [isingLineStoppedMean, isingLineStoppedKernel,
        isingLineCenteredFourth]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary (2 * m) p
      · rw [dif_pos hp]
        have h := ih p
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg ((p.1 : Real) - (m : Real))]
      · rw [dif_neg hp]
        have hw := ih (isingLineWest (2 * m) p)
        have he := ih (isingLineEast (2 * m) p hp)
        have hp0 : 0 < p.1 := by
          unfold isingLineBoxBoundary at hp
          omega
        calc
          _ <= (((((isingLineWest (2 * m) p).1 : Real) - (m : Real)) ^ 4 +
                  6 * (t : Real) *
                    (((isingLineWest (2 * m) p).1 : Real) - (m : Real)) ^ 2 +
                  3 * (t : Real) ^ 2) +
                ((((isingLineEast (2 * m) p hp).1 : Real) - (m : Real)) ^ 4 +
                  6 * (t : Real) *
                    (((isingLineEast (2 * m) p hp).1 : Real) - (m : Real)) ^ 2 +
                  3 * (t : Real) ^ 2)) / 2 := by
            exact div_le_div_of_nonneg_right (add_le_add hw he) (by norm_num)
          _ = ((p.1 : Real) - (m : Real)) ^ 4 +
                6 * (t : Real) * ((p.1 : Real) - (m : Real)) ^ 2 +
                6 * ((p.1 : Real) - (m : Real)) ^ 2 +
                3 * (t : Real) ^ 2 + 6 * (t : Real) + 1 := by
            unfold isingLineWest isingLineEast
            push_cast
            rw [Nat.cast_sub hp0]
            ring
          _ <= ((p.1 : Real) - (m : Real)) ^ 4 +
                6 * ((t + 1 : Nat) : Real) *
                  ((p.1 : Real) - (m : Real)) ^ 2 +
                3 * ((t + 1 : Nat) : Real) ^ 2 := by
            push_cast
            nlinarith



theorem isingLineStoppedKernel_center_boundary_le_fourth
    (m t : Nat) (hm : 0 < m) :
    isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ <=
      3 * (t : Real) ^ 2 / (m : Real) ^ 4 := by
  let center : IsingLineBox (2 * m) := ⟨m, by omega⟩
  let left : IsingLineBox (2 * m) := ⟨0, by omega⟩
  let right : IsingLineBox (2 * m) := ⟨2 * m, by omega⟩
  have hlr : left ≠ right := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [left, right] at hv
    omega
  have hmean := isingLineStoppedMean_centeredFourth_le m t center
  have hmean' :
      isingLineStoppedMean (2 * m) t (isingLineCenteredFourth m) center <=
        3 * (t : Real) ^ 2 := by
    simpa [center, isingLineCenteredFourth] using hmean
  have hboundary :
      (m : Real) ^ 4 *
          (isingLineStoppedKernel (2 * m) t center left +
            isingLineStoppedKernel (2 * m) t center right) <=
        isingLineStoppedMean (2 * m) t (isingLineCenteredFourth m) center := by
    calc
      _ = isingLineStoppedKernel (2 * m) t center left *
            isingLineCenteredFourth m left +
          isingLineStoppedKernel (2 * m) t center right *
            isingLineCenteredFourth m right := by
        simp [isingLineCenteredFourth, left, right]
        ring
      _ = ∑ q ∈ {left, right},
          isingLineStoppedKernel (2 * m) t center q *
            isingLineCenteredFourth m q := by
        rw [Finset.sum_pair hlr]
      _ <= ∑ q, isingLineStoppedKernel (2 * m) t center q *
          isingLineCenteredFourth m q := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro q
        exact mul_nonneg (isingLineStoppedKernel_nonneg _ _ _ _)
          (by unfold isingLineCenteredFourth; positivity)
      _ = _ := rfl
  have hm4 : 0 < (m : Real) ^ 4 := by positivity
  apply (le_div_iff₀ hm4).2
  calc
    (isingLineStoppedKernel (2 * m) t center left +
        isingLineStoppedKernel (2 * m) t center right) * (m : Real) ^ 4 =
      (m : Real) ^ 4 *
        (isingLineStoppedKernel (2 * m) t center left +
          isingLineStoppedKernel (2 * m) t center right) := by ring
    _ <= isingLineStoppedMean (2 * m) t
        (isingLineCenteredFourth m) center := hboundary
    _ <= 3 * (t : Real) ^ 2 := hmean'

end

end StatMech.Universality
