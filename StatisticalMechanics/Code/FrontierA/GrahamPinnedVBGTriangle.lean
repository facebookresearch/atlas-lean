/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamPinnedVBGPositivity
import Code.FrontierA.GrahamCorrections





open Finset
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace
open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem vbg_coordUp_eq_half_one_add_spin (m : V) (s : ConfigSpace V) :
    vbg_coordUp m s = (1 + spin s m) / 2 := by
  unfold vbg_coordUp spin
  by_cases h : s m <;> simp [h]

theorem vbg_exp_grahamZeroProb_one
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) :
    vbg_exp (grahamZeroProb E J) (fun _ => 1) = 1 := by
  unfold vbg_exp
  simpa using grahamZeroProb_sum_eq_one E J

theorem vbg_exp_grahamZeroProb_coordUp
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    vbg_exp (grahamZeroProb E J) (vbg_coordUp m) = 1 / 2 := by
  have hrewrite : (vbg_coordUp m : ConfigSpace V -> Real) =
      fun s => (1 / 2 : Real) * 1 + (1 / 2 : Real) * spin s m := by
    funext s
    rw [vbg_coordUp_eq_half_one_add_spin]
    ring
  rw [hrewrite, vbg_exp_add,
    vbg_exp_const_mul, vbg_exp_const_mul,
    vbg_exp_grahamZeroProb_one,
    vbg_exp_grahamZeroProb_eq_expJ,
    expJ_zero_spin_eq_zero]
  ring

theorem vbg_exp_grahamZeroProb_threeSpin_eq_zero
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (a b c : V) :
    vbg_exp (grahamZeroProb E J)
      (fun s => spin s a * spin s b * spin s c) = 0 := by
  let S := vbg_exp (grahamZeroProb E J)
    (fun s => spin s a * spin s b * spin s c)
  have hweight : ∀ s : ConfigSpace V,
      grahamZeroProb E J
          (StatMech.Sharpness.FieldGhostDict.flipV s) =
        grahamZeroProb E J s := by
    intro s
    unfold grahamZeroProb
    rw [show wJ E J (fun _ => 0)
        (StatMech.Sharpness.FieldGhostDict.flipV s) =
        wJ E J (fun _ => 0) s by
      simpa only [Pi.neg_apply, neg_zero] using
        ghsvp_wJ_negField_flip E J (fun _ => 0) s]
  have hneg : S = -S := by
    have hS : S = ∑ s : ConfigSpace V,
        grahamZeroProb E J
            (StatMech.Sharpness.FieldGhostDict.flipV s) *
          (spin (StatMech.Sharpness.FieldGhostDict.flipV s) a *
            spin (StatMech.Sharpness.FieldGhostDict.flipV s) b *
            spin (StatMech.Sharpness.FieldGhostDict.flipV s) c) :=
      (Equiv.sum_comp
        (StatMech.Sharpness.FieldGhostDict.flipV_involutive
          (V := V)).toPerm
        (fun s : ConfigSpace V => grahamZeroProb E J s *
          (spin s a * spin s b * spin s c))).symm
    simp_rw [hweight, StatMech.Sharpness.FieldGhostDict.spin_flipV] at hS
    rw [show (∑ s : ConfigSpace V,
        grahamZeroProb E J s *
          (-spin s a * -spin s b * -spin s c)) = -S by
      unfold S vbg_exp
      calc
        (∑ s : ConfigSpace V, grahamZeroProb E J s *
            (-spin s a * -spin s b * -spin s c)) =
            ∑ s : ConfigSpace V,
              -(grahamZeroProb E J s *
                (spin s a * spin s b * spin s c)) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
        _ = -(∑ s : ConfigSpace V, grahamZeroProb E J s *
              (spin s a * spin s b * spin s c)) :=
          by
            simpa using Finset.sum_neg_distrib
              (s := Finset.univ)
              (f := fun s : ConfigSpace V => grahamZeroProb E J s *
                (spin s a * spin s b * spin s c))
        _ = _ := rfl] at hS
    exact hS
  dsimp [S] at hneg
  linarith

theorem vbg_exp_grahamZeroProb_twoSpin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (a b : V) :
    vbg_exp (grahamZeroProb E J) (fun s => spin s a * spin s b) =
      grahamTwoPoint E J a b := by
  rw [vbg_exp_grahamZeroProb_eq_expJ]
  exact (grahamTwoPoint_eq_expJ E J a b).symm

theorem vbg_exp_grahamZeroProb_mul_coordUp
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (f : ConfigSpace V -> Real) :
    (∑ s : ConfigSpace V,
        grahamZeroProb E J s * vbg_coordUp m s * f s) =
      (vbg_exp (grahamZeroProb E J) f +
        vbg_exp (grahamZeroProb E J) (fun s => f s * spin s m)) / 2 := by
  calc
    (∑ s : ConfigSpace V,
        grahamZeroProb E J s * vbg_coordUp m s * f s) =
        ∑ s : ConfigSpace V,
          (grahamZeroProb E J s * f s +
            grahamZeroProb E J s * (f s * spin s m)) / 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [vbg_coordUp_eq_half_one_add_spin]
      ring
    _ = ((∑ s : ConfigSpace V, grahamZeroProb E J s * f s) +
        ∑ s : ConfigSpace V,
          grahamZeroProb E J s * (f s * spin s m)) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    _ = _ := rfl

theorem vbg_exp_grahamPinnedProb
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (f : ConfigSpace V -> Real) :
    vbg_exp (grahamPinnedProb E J m) f =
      vbg_exp (grahamZeroProb E J) f +
        vbg_exp (grahamZeroProb E J) (fun s => f s * spin s m) := by
  unfold grahamPinnedProb
  rw [vbg_expPlus_eq,
    vbg_exp_grahamZeroProb_mul_coordUp,
    vbg_exp_grahamZeroProb_coordUp]
  ring

theorem vbg_exp_grahamPinnedProb_spin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m a : V) :
    vbg_exp (grahamPinnedProb E J m) (fun s => spin s a) =
      grahamTwoPoint E J a m := by
  rw [vbg_exp_grahamPinnedProb,
    vbg_exp_grahamZeroProb_eq_expJ,
    expJ_zero_spin_eq_zero,
    zero_add,
    vbg_exp_grahamZeroProb_twoSpin]

theorem vbg_exp_grahamPinnedProb_twoSpin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m a b : V) :
    vbg_exp (grahamPinnedProb E J m)
        (fun s => spin s a * spin s b) =
      grahamTwoPoint E J a b := by
  rw [vbg_exp_grahamPinnedProb,
    vbg_exp_grahamZeroProb_twoSpin,
    vbg_exp_grahamZeroProb_threeSpin_eq_zero,
    add_zero]

theorem vbg_cov_grahamPinnedProb_spin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m a b : V) :
    vbg_cov (grahamPinnedProb E J m)
        (fun s => spin s a) (fun s => spin s b) =
      grahamBridgeGap E J a b m := by
  unfold vbg_cov grahamBridgeGap
  rw [vbg_exp_grahamPinnedProb_twoSpin,
    vbg_exp_grahamPinnedProb_spin,
    vbg_exp_grahamPinnedProb_spin,
    grahamTwoPoint_comm E J b m]

theorem vbg_var_grahamPinnedProb_spin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m k : V) :
    vbg_var (grahamPinnedProb E J m) (fun s => spin s k) =
      1 - grahamTwoPoint E J k m ^ 2 := by
  unfold vbg_var vbg_cov
  rw [show (fun s : ConfigSpace V => spin s k * spin s k) =
      (fun _ => 1) by funext s; rw [spin_sq],
    show vbg_exp (grahamPinnedProb E J m) (fun _ => 1) = 1 by
      unfold grahamPinnedProb
      simpa [vbg_exp] using vbg_condPlus_norm
        (π := grahamZeroProb E J) (Y := vbg_coordUp m) (by
          rw [vbg_exp_grahamZeroProb_coordUp]
          norm_num),
    vbg_exp_grahamPinnedProb_spin]
  ring

theorem grahamPinnedProb_FKG
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e) (m : V) :
    StatMech.FKGLatticeCondition (grahamPinnedProb E J m) := by
  unfold grahamPinnedProb
  refine vbg_condPlus_FKG
    (π := grahamZeroProb E J) (Y := vbg_coordUp m)
    (grahamZeroProb_nonneg E J) ?_ (grahamZeroProb_FKG E J hJ)
    (vbg_coordUp_logSupermod m) ?_
  · intro s
    unfold vbg_coordUp
    by_cases h : s m <;> simp [h]
  · rw [vbg_exp_grahamZeroProb_coordUp]
    norm_num

theorem vbg_cov_comm
    (mu : ConfigSpace V -> Real) (f g : ConfigSpace V -> Real) :
    vbg_cov mu f g = vbg_cov mu g f := by
  unfold vbg_cov
  have hfg : (fun s => f s * g s) = (fun s => g s * f s) := by
    funext s
    ring
  rw [hfg]
  ring



theorem grahamBridgeGap_triangle
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e) (i k j m : V) :
    grahamBridgeGap E J i k m * grahamBridgeGap E J j k m <=
      (1 - grahamTwoPoint E J k m ^ 2) *
        grahamBridgeGap E J i j m := by
  by_cases hkm : k = m
  · subst k
    simp [grahamBridgeGap]
  · let mu := grahamPinnedProb E J m
    have hmu0 : (0 : ConfigSpace V -> Real) <= mu :=
      grahamPinnedProb_nonneg E J m
    have hmu1 : ∑ s, mu s = 1 := grahamPinnedProb_sum_eq_one E J m
    have hmuFKG : StatMech.FKGLatticeCondition mu :=
      grahamPinnedProb_FKG E J hJ m
    obtain ⟨hpk0, hpk1⟩ := grahamPinned_coordUp_pos_lt_one
      (m := m) (k := k) E J (fun h => hkm h.symm)
    have htriangle := vbg_thm1_configSpace hmu0 hmu1 hmuFKG k
      (X := fun s => spin s i) (Z := fun s => spin s j)
      (vbg_spin_monotone i) (vbg_spin_monotone j)
      (by simpa only [mu] using hpk0) (by simpa only [mu] using hpk1)
    have hik : grahamBridgeGap E J i k m =
        2 * vbg_cov mu (fun s => spin s i) (vbg_coordUp k) := by
      rw [← vbg_cov_grahamPinnedProb_spin E J m i k]
      have heq : (fun s : ConfigSpace V => spin s k) =
          fun s => 2 * vbg_coordUp k s + (-1) := by
        funext s
        rw [vbg_spin_eq_coordUp]
        ring
      rw [heq, vbg_cov_affine_right mu hmu1
        (fun s => spin s i) (vbg_coordUp k) 2 (-1)]
    have hjk : grahamBridgeGap E J j k m =
        2 * vbg_cov mu (vbg_coordUp k) (fun s => spin s j) := by
      rw [← vbg_cov_grahamPinnedProb_spin E J m j k,
        vbg_cov_comm]
      have heq : (fun s : ConfigSpace V => spin s k) =
          fun s => 2 * vbg_coordUp k s + (-1) := by
        funext s
        rw [vbg_spin_eq_coordUp]
        ring
      rw [heq, vbg_cov_affine_left mu hmu1
        (vbg_coordUp k) (fun s => spin s j) 2 (-1)]
    have hij : grahamBridgeGap E J i j m =
        vbg_cov mu (fun s => spin s i) (fun s => spin s j) := by
      exact (vbg_cov_grahamPinnedProb_spin E J m i j).symm
    have hvar : 1 - grahamTwoPoint E J k m ^ 2 =
        4 * vbg_var mu (vbg_coordUp k) := by
      rw [← vbg_var_grahamPinnedProb_spin E J m k]
      unfold vbg_var
      have heq : (fun s : ConfigSpace V => spin s k) =
          fun s => 2 * vbg_coordUp k s + (-1) := by
        funext s
        rw [vbg_spin_eq_coordUp]
        ring
      rw [heq, vbg_cov_affine_left mu hmu1
        (vbg_coordUp k) _ 2 (-1),
        vbg_cov_affine_right mu hmu1 _ (vbg_coordUp k) 2 (-1)]
      ring
    rw [hik, hjk, hij, hvar]
    nlinarith

end StatMech.FrontierA
