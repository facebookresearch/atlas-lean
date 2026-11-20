/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamHeadlineAdapter
import Code.FrontierA.GrahamGraphAdapter
import Code.FrontierA.GrahamPinnedVBGTriangle











open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace
open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamAnchorCoupling (J : Sym2 V -> Real) (m : V) (e : Sym2 V) : Real :=
  if m ∈ e then 0 else J e


def grahamAnchorField (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (m x : V) : Real :=
  if x = m then 0 else if s(x, m) ∈ E then J s(x, m) else 0

theorem grahamAnchorCoupling_nonneg (J : Sym2 V -> Real) (m : V)
    (hJ : forall e, 0 <= J e) :
    forall e, 0 <= grahamAnchorCoupling J m e := by
  intro e
  simp only [grahamAnchorCoupling]
  split <;> simp [hJ]

theorem grahamAnchorField_nonneg (E : Finset (Sym2 V))
    (J : Sym2 V -> Real) (m : V) (hJ : forall e, 0 <= J e) :
    forall x, 0 <= grahamAnchorField E J m x := by
  intro x
  by_cases hxm : x = m
  · simp [grahamAnchorField, hxm]
  · by_cases hE : s(x, m) ∈ E
    · simp [grahamAnchorField, hxm, hE, hJ]
    · simp [grahamAnchorField, hxm, hE]


def grahamPinConfig (m : V) (t : ConfigSpace V) : ConfigSpace V :=
  Function.update t m true

@[simp] theorem grahamPinConfig_at (m : V) (t : ConfigSpace V) :
    grahamPinConfig m t m = true := by
  simp [grahamPinConfig]

@[simp] theorem grahamPinConfig_of_ne (m : V) (t : ConfigSpace V)
    {x : V} (hxm : x ≠ m) :
    grahamPinConfig m t x = t x := by
  simp [grahamPinConfig, hxm]

theorem spin_grahamPinConfig_at (m : V) (t : ConfigSpace V) :
    spin (grahamPinConfig m t) m = 1 := by
  simp [spin]

theorem spin_grahamPinConfig_of_ne (m : V) (t : ConfigSpace V)
    {x : V} (hxm : x ≠ m) :
    spin (grahamPinConfig m t) x = spin t x := by
  simp [spin, grahamPinConfig, hxm]



theorem grahamAnchor_incidentSum
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V) (t : ConfigSpace V) :
    (∑ e ∈ E.filter (fun e => m ∈ e),
        J e * bond (grahamPinConfig m t) e) =
      ∑ x, grahamAnchorField E J m x * spin t x := by
  classical
  let N : Finset V := Finset.univ.filter (fun x => x ≠ m ∧ s(x, m) ∈ E)
  have hfield :
      (∑ x, grahamAnchorField E J m x * spin t x) =
        ∑ x ∈ N, J s(x, m) * spin t x := by
    classical
    simp only [N, Finset.sum_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxm : x = m
    · simp [grahamAnchorField, hxm]
    · by_cases hE : s(x, m) ∈ E <;> simp [grahamAnchorField, hxm, hE]
  rw [hfield]
  symm
  apply Finset.sum_bij (fun x _ => s(x, m))
  · intro x hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter]
    exact ⟨hx.2, Sym2.mem_mk_right x m⟩
  · intro x hx y hy hxy
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [Sym2.eq_iff] at hxy
    rcases hxy with h | h
    · exact h.1
    · exact False.elim (hx.1 h.1)
  · intro e he
    simp only [Finset.mem_filter] at he
    induction e using Sym2.ind with
    | _ x y =>
        simp only [Sym2.mem_iff] at he
        rcases he.2 with rfl | rfl
        · refine ⟨y, ?_, by simpa [Sym2.eq_swap]⟩
          have hne : y ≠ m := by
            intro hym
            subst y
            exact hdiag s(m, m) he.1 (Sym2.mk_isDiag_iff.mpr rfl)
          simp [N, hne, he.1, Sym2.eq_swap]
        · refine ⟨x, ?_, rfl⟩
          have hne : x ≠ m := by
            intro hxm
            subst x
            exact hdiag s(m, m) he.1 (Sym2.mk_isDiag_iff.mpr rfl)
          simp [N, hne, he.1]
  · intro x hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [bond_mk, spin_grahamPinConfig_of_ne m t hx.1,
      spin_grahamPinConfig_at]
    ring



theorem grahamAnchor_nonincidentSum
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (m : V) (t : ConfigSpace V) :
    (∑ e ∈ E, grahamAnchorCoupling J m e * bond t e) =
      ∑ e ∈ E.filter (fun e => m ∉ e), J e * bond t e := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hme : m ∈ e <;> simp [grahamAnchorCoupling, hme]



theorem grahamAnchor_weight_eq_pin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V) (t : ConfigSpace V) :
    wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) t =
      wJ E J (fun _ => 0) (grahamPinConfig m t) := by
  unfold wJ
  congr 1
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [grahamAnchor_nonincidentSum, ← grahamAnchor_incidentSum E J hdiag]
  have hnonincident :
      (∑ e ∈ E.filter (fun e => m ∉ e),
          J e * bond (grahamPinConfig m t) e) =
        ∑ e ∈ E.filter (fun e => m ∉ e), J e * bond t e := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [Finset.mem_filter] at he
    induction e using Sym2.ind with
    | _ x y =>
        simp only [Sym2.mem_iff, not_or] at he
        have hxm : x ≠ m := fun h => he.2.1 h.symm
        have hym : y ≠ m := fun h => he.2.2 h.symm
        rw [bond_mk, bond_mk, spin_grahamPinConfig_of_ne m t hxm,
          spin_grahamPinConfig_of_ne m t hym]
  rw [← hnonincident]
  have hsplit := Finset.sum_filter_add_sum_filter_not E
    (fun e => m ∈ e) (fun e => J e * bond (grahamPinConfig m t) e)
  simpa only [add_comm] using hsplit



def grahamAnchorSlice (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) : ConfigSpace V :=
  (Equiv.funSplitAt m Bool).symm (b, eta)

@[simp] theorem grahamAnchorSlice_at (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) :
    grahamAnchorSlice m b eta m = b := by
  simp [grahamAnchorSlice, Equiv.funSplitAt, Equiv.piSplitAt]

@[simp] theorem grahamAnchorSlice_ne (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) (x : {x : V // x ≠ m}) :
    grahamAnchorSlice m b eta x.1 = eta x := by
  simp [grahamAnchorSlice, Equiv.funSplitAt, Equiv.piSplitAt, x.2]

theorem grahamPinConfig_anchorSlice (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) :
    grahamPinConfig m (grahamAnchorSlice m b eta) =
      grahamAnchorSlice m true eta := by
  funext x
  by_cases hxm : x = m
  · subst x
    simp
  · let y : {x : V // x ≠ m} := ⟨x, hxm⟩
    rw [grahamPinConfig_of_ne m _ hxm]
    exact (grahamAnchorSlice_ne m b eta y).trans
      (grahamAnchorSlice_ne m true eta y).symm


theorem grahamAnchor_sum_eq_two_mul_trueSlice
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : ∀ t, F (grahamPinConfig m t) = F t) :
    (∑ t : ConfigSpace V,
        F t * wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) t) =
      2 * ∑ eta : {x : V // x ≠ m} -> Bool,
        F (grahamAnchorSlice m true eta) *
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt m Bool).symm]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hslice (b : Bool) (eta : {x : V // x ≠ m} -> Bool) :
      F (grahamAnchorSlice m b eta) *
          wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
            (grahamAnchorSlice m b eta) =
        F (grahamAnchorSlice m true eta) *
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
    rw [← hF (grahamAnchorSlice m b eta),
      grahamAnchor_weight_eq_pin E J hdiag,
      grahamPinConfig_anchorSlice]
  simp only [grahamAnchorSlice] at hslice ⊢
  simp_rw [hslice]
  ring


theorem graham_trueSlice_sum_eq_half_Z
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    (∑ eta : {x : V // x ≠ m} -> Bool,
        wJ E J (fun _ => 0) (grahamAnchorSlice m true eta)) =
      ZJ E J (fun _ => 0) / 2 := by
  have hhalf := vbg_exp_grahamZeroProb_coordUp E J m
  have hslice :
      (∑ s : ConfigSpace V,
          wJ E J (fun _ => 0) s * vbg_coordUp m s) =
        ∑ eta : {x : V // x ≠ m} -> Bool,
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
    rw [← Equiv.sum_comp (Equiv.funSplitAt m Bool).symm]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [grahamAnchorSlice]
    simp [vbg_coordUp, Equiv.funSplitAt, Equiv.piSplitAt]
  unfold vbg_exp grahamZeroProb at hhalf
  rw [show (∑ s : ConfigSpace V,
      wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0) * vbg_coordUp m s) =
      (∑ s : ConfigSpace V,
        wJ E J (fun _ => 0) s * vbg_coordUp m s) /
          ZJ E J (fun _ => 0) by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring,
    hslice] at hhalf
  have hZ : ZJ E J (fun _ => 0) ≠ 0 := (ZJ_pos E J (fun _ => 0)).ne'
  field_simp [hZ] at hhalf ⊢
  linarith



theorem grahamAnchor_ZJ_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V) :
    ZJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) =
      ZJ E J (fun _ => 0) := by
  unfold ZJ
  have hsum := grahamAnchor_sum_eq_two_mul_trueSlice E J hdiag m
    (fun _ => (1 : Real)) (by intro t; rfl)
  simp only [one_mul] at hsum
  rw [hsum, graham_trueSlice_sum_eq_half_Z]
  simp [ZJ]
  ring


theorem vbg_exp_grahamPinnedProb_eq_trueSlice
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (F : ConfigSpace V -> Real) :
    vbg_exp (grahamPinnedProb E J m) F =
      (2 * ∑ eta : {x : V // x ≠ m} -> Bool,
        F (grahamAnchorSlice m true eta) *
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta)) /
        ZJ E J (fun _ => 0) := by
  rw [vbg_exp_grahamPinnedProb_eq,
    grahamZeroProb_coordUp_eq_half]
  have hslice :
      (∑ s : ConfigSpace V,
          wJ E J (fun _ => 0) s * (vbg_coordUp m s * F s)) =
        ∑ eta : {x : V // x ≠ m} -> Bool,
          F (grahamAnchorSlice m true eta) *
            wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
    rw [← Equiv.sum_comp (Equiv.funSplitAt m Bool).symm]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [grahamAnchorSlice]
    simp [vbg_coordUp, Equiv.funSplitAt, Equiv.piSplitAt]
    apply Finset.sum_congr rfl
    intro eta _
    ring
  unfold vbg_exp grahamZeroProb
  rw [show (∑ s : ConfigSpace V,
      wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0) *
        (vbg_coordUp m s * F s)) =
      (∑ s : ConfigSpace V,
        wJ E J (fun _ => 0) s * (vbg_coordUp m s * F s)) /
          ZJ E J (fun _ => 0) by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring,
    hslice]
  have hZ : ZJ E J (fun _ => 0) ≠ 0 := (ZJ_pos E J (fun _ => 0)).ne'
  field_simp [hZ]


theorem grahamAnchor_expJ_eq_pinned
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : ∀ t, F (grahamPinConfig m t) = F t) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) F =
      vbg_exp (grahamPinnedProb E J m) F := by
  unfold expJ
  rw [grahamAnchor_ZJ_eq E J hdiag m,
    grahamAnchor_sum_eq_two_mul_trueSlice E J hdiag m F hF,
    vbg_exp_grahamPinnedProb_eq_trueSlice]



theorem grahamAnchor_onePoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m x : V} (hxm : x ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => spin t x) =
      grahamTwoPoint E J x m := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m]
  · exact vbg_exp_grahamPinnedProb_spin E J m x
  · intro t
    rw [spin_grahamPinConfig_of_ne m t hxm]



theorem grahamAnchor_twoPoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m x y : V}
    (hxm : x ≠ m) (hym : y ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => spin t x * spin t y) =
      grahamTwoPoint E J x y := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m]
  · exact vbg_exp_grahamPinnedProb_twoSpin E J m x y
  · intro t
    rw [spin_grahamPinConfig_of_ne m t hxm,
      spin_grahamPinConfig_of_ne m t hym]


theorem vbg_exp_grahamPinnedProb_threeSpin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m i j k : V) :
    vbg_exp (grahamPinnedProb E J m)
        (fun t => spin t i * (spin t j * spin t k)) =
      grahamFourPoint E J i j k m := by
  rw [vbg_exp_grahamPinnedProb E J m]
  have hzero := vbg_exp_grahamZeroProb_threeSpin_eq_zero E J i j k
  rw [show (fun t : ConfigSpace V => spin t i * (spin t j * spin t k)) =
      (fun t => spin t i * spin t j * spin t k) by
        funext t; ring,
    hzero, zero_add,
    vbg_exp_grahamZeroProb_eq_expJ,
    grahamFourPoint_eq_expJ]
  congr 1
  funext t
  ring



theorem grahamAnchor_threePoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => spin t i * (spin t j * spin t k)) =
      grahamFourPoint E J i j k m := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m]
  · exact vbg_exp_grahamPinnedProb_threeSpin E J m i j k
  · intro t
    rw [spin_grahamPinConfig_of_ne m t him,
      spin_grahamPinConfig_of_ne m t hjm,
      spin_grahamPinConfig_of_ne m t hkm]

end StatMech.FrontierA
