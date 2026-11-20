/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzFourPoint
import Code.Ising.LebowitzPfisterReflectionGauge
import Code.Ising.LebowitzPfisterStrongMarkedSite

open Finset
open scoped BigOperators

namespace StatMech.Ising

open StatMech.Sharpness StatMech.FrontierA
open StatMech.Sharpness.FieldGhostDict

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



def lpGhostCoupling (J : Sym2 V -> Real) (hf : V -> Real) :
    Sym2 (Option V) -> Real :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | some x, some y => J s(x, y)
    | some x, none => hf x
    | none, some y => hf y
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩

@[simp] theorem lpGhostCoupling_some_some
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) :
    lpGhostCoupling J hf s(some x, some y) = J s(x, y) := rfl

@[simp] theorem lpGhostCoupling_some_none
    (J : Sym2 V -> Real) (hf : V -> Real) (x : V) :
    lpGhostCoupling J hf s(some x, none) = hf x := rfl

theorem lpGhost_couplingSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (s : ConfigSpace (Option V)) :
    (∑ e ∈ (withGhost G).edgeFinset,
        lpGhostCoupling J hf e * bond s e) =
      (∑ e ∈ G.edgeFinset,
        J e * bond (fun x => s (some x)) e) +
      spin s none * ∑ x : V, hf x * spin s (some x) := by
  rw [FieldGhostDict.withGhost_edgeFinset_eq,
    Finset.sum_union (FieldGhostDict.disjoint_orig_ghost G)]
  congr 1
  · rw [FieldGhostDict.origEdges, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e _
      induction e with
      | h x y =>
          rw [Sym2.map_mk, lpGhostCoupling_some_some, bond_mk, bond_mk]
          rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective V) hab
  · rw [FieldGhostDict.ghostEdges, Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [lpGhostCoupling_some_none, bond_mk]
      ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with h | h
      · exact Option.some_injective V h.1
      · exact absurd h.2 (by simp)



theorem lpGhost_weight_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (s : ConfigSpace (Option V)) :
    wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0) s =
      wJ G.edgeFinset J (fun x => hf x * spin s none)
        (fun x => s (some x)) := by
  unfold wJ
  rw [lpGhost_couplingSum]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change spin s none * (hf x * spin s (some x)) =
    hf x * spin s none * spin s (some x)
  ring



theorem lpGhost_ZJ_eq_two_mul
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) :
    ZJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0) =
      2 * ZJ G.edgeFinset J hf := by
  change (∑ s : ConfigSpace (Option V),
      wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0) s) =
    2 * ZJ G.edgeFinset J hf
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have htrue :
      (∑ tau : ConfigSpace V,
        wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0)
          (fun z => Option.rec true tau z)) = ZJ G.edgeFinset J hf := by
    unfold ZJ
    apply Finset.sum_congr rfl
    intro tau _
    rw [lpGhost_weight_eq]
    congr 2
    funext x
    simp [FieldGhostDict.split_ghost_spin]
  have hfalse :
      (∑ tau : ConfigSpace V,
        wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0)
          (fun z => Option.rec false tau z)) =
        ZJ G.edgeFinset J (fun x => -hf x) := by
    unfold ZJ
    apply Finset.sum_congr rfl
    intro tau _
    rw [lpGhost_weight_eq]
    congr 2
    funext x
    simp [FieldGhostDict.split_ghost_spin]
  rw [htrue, hfalse, ghsvp_ZJ_negField]
  ring

theorem lp_negField_even_numerator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> Real)
    (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
    (∑ s : ConfigSpace V,
      F s * wJ G.edgeFinset J (fun x => -hf x) s) =
      ∑ s : ConfigSpace V, F s * wJ G.edgeFinset J hf s := by
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive (V := V)).toPerm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Function.Involutive.coe_toPerm]
  rw [hF, ghsvp_wJ_negField_flip]



theorem lpGhost_even_expJ_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> Real)
    (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
    expJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0)
        (fun s => F (fun x => s (some x))) =
      expJ G.edgeFinset J hf F := by
  unfold expJ
  rw [lpGhost_ZJ_eq_two_mul]
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have htrue :
      (∑ tau : ConfigSpace V,
        F (fun x => (fun z => Option.rec true tau z) (some x)) *
          wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0)
            (fun z => Option.rec true tau z)) =
        ∑ tau : ConfigSpace V, F tau * wJ G.edgeFinset J hf tau := by
    apply Finset.sum_congr rfl
    intro tau _
    rw [lpGhost_weight_eq]
    simp [FieldGhostDict.split_ghost_spin]
  have hfalse :
      (∑ tau : ConfigSpace V,
        F (fun x => (fun z => Option.rec false tau z) (some x)) *
          wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0)
            (fun z => Option.rec false tau z)) =
        ∑ tau : ConfigSpace V,
          F tau * wJ G.edgeFinset J (fun x => -hf x) tau := by
    apply Finset.sum_congr rfl
    intro tau _
    rw [lpGhost_weight_eq]
    simp [FieldGhostDict.split_ghost_spin]
  rw [htrue, hfalse, lp_negField_even_numerator G J hf F hF]
  have hZ : ZJ G.edgeFinset J hf ≠ 0 := (ZJ_pos _ _ _).ne'
  field_simp
  ring



theorem lpGhost_twoPoint_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) :
    grahamTwoPoint (withGhost G).edgeFinset (lpGhostCoupling J hf)
        (some x) (some y) =
      expJ G.edgeFinset J hf (fun s => spin s x * spin s y) := by
  rw [grahamTwoPoint_eq_expJ]
  simpa only using lpGhost_even_expJ_eq G J hf
    (fun s => spin s x * spin s y) (by
      intro s
      simp only [FieldGhostDict.spin_flipV]
      ring)


theorem lpGhost_fourPoint_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (i j k l : V) :
    grahamFourPoint (withGhost G).edgeFinset (lpGhostCoupling J hf)
        (some i) (some j) (some k) (some l) =
      expJ G.edgeFinset J hf
        (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
  rw [grahamFourPoint_eq_expJ]
  simpa only using lpGhost_even_expJ_eq G J hf
    (fun s => (spin s i * spin s j) * (spin s k * spin s l)) (by
      intro s
      simp only [FieldGhostDict.spin_flipV]
      ring)


def lpFieldUrsell4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (i j k l : V) : Real :=
  expJ G.edgeFinset J hf
      (fun s => (spin s i * spin s j) * (spin s k * spin s l)) -
    expJ G.edgeFinset J hf (fun s => spin s i * spin s j) *
      expJ G.edgeFinset J hf (fun s => spin s k * spin s l) -
    expJ G.edgeFinset J hf (fun s => spin s i * spin s k) *
      expJ G.edgeFinset J hf (fun s => spin s j * spin s l) -
    expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
      expJ G.edgeFinset J hf (fun s => spin s j * spin s k)

theorem lpGhost_ursell4_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (i j k l : V) :
    grahamUrsell4 (withGhost G).edgeFinset (lpGhostCoupling J hf)
        (some i) (some j) (some k) (some l) =
      lpFieldUrsell4 G J hf i j k l := by
  unfold grahamUrsell4 lpFieldUrsell4
  rw [lpGhost_fourPoint_eq,
    lpGhost_twoPoint_eq, lpGhost_twoPoint_eq, lpGhost_twoPoint_eq,
    lpGhost_twoPoint_eq, lpGhost_twoPoint_eq, lpGhost_twoPoint_eq]

theorem lpGhostCoupling_nonneg
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x) :
    forall e, 0 <= lpGhostCoupling J hf e := by
  intro e
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y <;>
        simp [lpGhostCoupling, hJ, hhf]



theorem lpField_lebowitz_four_point_le_leading
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x)
    (i j k l : V)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    lpFieldUrsell4 G J hf i j k l <=
      -2 *
        (expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
          expJ G.edgeFinset J hf (fun s => spin s j * spin s l) *
          expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) := by
  have hlead := lebowitz_four_point_le_leading (withGhost G)
    (lpGhostCoupling J hf) (lpGhostCoupling_nonneg J hf hJ hhf)
    (some i) (some j) (some k) (some l)
    (by simpa) (by simpa) (by simpa) (by simpa) (by simpa) (by simpa)
  rw [lpGhost_ursell4_eq,
    lpGhost_twoPoint_eq, lpGhost_twoPoint_eq, lpGhost_twoPoint_eq] at hlead
  exact hlead



theorem lpField_graham_four_point_strong
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x)
    (i j k l : V) :
    2 * expJ G.edgeFinset J hf (fun s => spin s k * spin s l) *
        (expJ G.edgeFinset J hf (fun s => spin s i * spin s k) -
          expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) *
        (expJ G.edgeFinset J hf (fun s => spin s j * spin s k) -
          expJ G.edgeFinset J hf (fun s => spin s j * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) <=
      (1 - expJ G.edgeFinset J hf (fun s => spin s k * spin s l) ^ 2) *
        (-(lpFieldUrsell4 G J hf i j k l +
          2 * (expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s j * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s k * spin s l)))) := by
  have h := grahamMarkedSite_four_point_strong (withGhost G)
    (lpGhostCoupling J hf) (lpGhostCoupling_nonneg J hf hJ hhf)
    (some i) (some j) (some k) (some l)
  rw [lpGhost_ursell4_eq] at h
  unfold grahamBridgeGap at h
  simp only [lpGhost_twoPoint_eq] at h
  simpa [mul_comm] using h

end

end StatMech.Ising
