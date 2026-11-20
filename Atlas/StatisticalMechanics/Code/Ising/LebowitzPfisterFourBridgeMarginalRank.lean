/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterAgreementMarginalRatio
import Code.Ising.LebowitzPfisterFourBridgeActual










open Finset SimpleGraph

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def agreementConfigFinsetEquiv : ConfigSpace V ≃ Finset V where
  toFun := ghsLAgreeFinset
  invFun := fun S v => decide (v ∈ S)
  left_inv := by
    intro q
    funext v
    cases hq : q v <;> simp [ghsLAgreeFinset, hq]
  right_inv := by
    intro S
    ext v
    simp [ghsLAgreeFinset]

@[simp] theorem agreementConfigFinsetEquiv_apply (q : ConfigSpace V) :
    agreementConfigFinsetEquiv q = ghsLAgreeFinset q := rfl

@[simp] theorem agreementConfigFinsetEquiv_symm_apply (S : Finset V) (v : V) :
    agreementConfigFinsetEquiv.symm S v = decide (v ∈ S) := rfl



def ghsiAgreementMarginalProb
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (M P : Finset V) : Real :=
  ∑ q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
      (fun q => ghsLAgreeFinset q ∩ M = P),
    ghsiAgreementProb G J hf q



theorem ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {M P : Finset V} (hPM : P ⊆ M) :
    ghsiSubsetMarginalMass G J hf M P =
      ((4 * Fintype.card (ConfigSpace V) : Real) *
          (ZJ G.edgeFinset J hf) ^ 2) *
        ghsiAgreementMarginalProb G J hf M P := by
  classical
  let C : Real := 4 * Fintype.card (ConfigSpace V)
  have hscale (A : Finset V) :
      ghsiSubsetMass G J hf A =
        C * ghsiFibreMass G J hf (agreementConfigFinsetEquiv.symm A) := by
    have h := ghsiSubsetMass_agreeFinset_eq_mul_fibreMass
      G J hf (agreementConfigFinsetEquiv.symm A)
    have hagree :
        ghsLAgreeFinset (agreementConfigFinsetEquiv.symm A) = A :=
      agreementConfigFinsetEquiv.apply_symm_apply A
    rw [hagree] at h
    exact h
  have hreindex :
      (∑ S ∈ Mᶜ.powerset,
          ghsiFibreMass G J hf
            (agreementConfigFinsetEquiv.symm (P ∪ S))) =
        ∑ q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
            (fun q => ghsLAgreeFinset q ∩ M = P),
          ghsiFibreMass G J hf q := by
    apply Finset.sum_bij
      (fun S _ => agreementConfigFinsetEquiv.symm (P ∪ S))
    · intro S hS
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hSc : S ⊆ Mᶜ := Finset.mem_powerset.mp hS
      have hagree :
          ghsLAgreeFinset
              (agreementConfigFinsetEquiv.symm (P ∪ S)) = P ∪ S :=
        agreementConfigFinsetEquiv.apply_symm_apply (P ∪ S)
      rw [hagree]
      ext v
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hvP | hvS, hvM⟩
        · exact hvP
        · exact False.elim ((mem_compl.mp (hSc hvS)) hvM)
      · intro hvP
        exact ⟨Or.inl hvP, hPM hvP⟩
    · intro S hS T hT hEq
      apply Finset.ext
      intro v
      have hsets : P ∪ S = P ∪ T := by
        exact agreementConfigFinsetEquiv.symm.injective hEq
      have hSc : S ⊆ Mᶜ := Finset.mem_powerset.mp hS
      have hTc : T ⊆ Mᶜ := Finset.mem_powerset.mp hT
      constructor
      · intro hvS
        have hvU : v ∈ P ∪ T := by
          rw [← hsets]
          exact mem_union_right P hvS
        rcases mem_union.mp hvU with hvP | hvT
        · exact False.elim ((mem_compl.mp (hSc hvS)) (hPM hvP))
        · exact hvT
      · intro hvT
        have hvU : v ∈ P ∪ S := by
          rw [hsets]
          exact mem_union_right P hvT
        rcases mem_union.mp hvU with hvP | hvS
        · exact False.elim ((mem_compl.mp (hTc hvT)) (hPM hvP))
        · exact hvS
    · intro q hq
      have hqM : ghsLAgreeFinset q ∩ M = P :=
        (Finset.mem_filter.mp hq).2
      let S := ghsLAgreeFinset q \ M
      have hSc : S ⊆ Mᶜ := by
        intro v hv
        exact mem_compl.mpr (mem_sdiff.mp hv).2
      refine ⟨S, Finset.mem_powerset.mpr hSc, ?_⟩
      apply agreementConfigFinsetEquiv.injective
      rw [Equiv.apply_symm_apply]
      change P ∪ S = ghsLAgreeFinset q
      ext v
      simp only [mem_union]
      constructor
      · intro hv
        rcases hv with hvP | hvS
        · have hvPi : v ∈ ghsLAgreeFinset q ∩ M := by
            rw [hqM]
            exact hvP
          exact (mem_inter.mp hvPi).1
        · exact (mem_sdiff.mp hvS).1
      · intro hvq
        by_cases hvM : v ∈ M
        · left
          have hi : v ∈ ghsLAgreeFinset q ∩ M :=
            mem_inter.mpr ⟨hvq, hvM⟩
          rw [hqM] at hi
          exact hi
        · right
          exact mem_sdiff.mpr ⟨hvq, hvM⟩
    · intro S hS
      rfl
  unfold ghsiSubsetMarginalMass ghsiAgreementMarginalProb
  simp_rw [hscale]
  rw [← Finset.mul_sum, hreindex]
  simp_rw [ghsiAgreementProb]
  rw [← Finset.sum_div]
  have hZ : ZJ G.edgeFinset J hf ≠ 0 := (ZJ_pos _ _ _).ne'
  field_simp [hZ]
  ring


def fourBridgeMarkedSet (w x y z : V) : Finset V := {w, x, y, z}



def fourBridgeAgreementSpinMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (w x y z : V) (s : Real) : Real :=
  ∑ q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
      (fun q => replicaAgreementSpin (fourBridgeSites w x y z) q = s),
    ghsiAgreementProb G J hf q

theorem replicaAgreementSpin_fourBridgeSites (q : ConfigSpace V)
    (w x y z : V) :
    replicaAgreementSpin (fourBridgeSites w x y z) q =
      spin q w + spin q x + spin q y + spin q z := by
  unfold replicaAgreementSpin
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp
  ring

theorem replicaBridgeInteraction_fourBridgeSites
    (a b : ConfigSpace V) (w x y z : V) :
    replicaBridgeInteraction (fourBridgeSites w x y z) a b =
      spin a w * spin b w + spin a x * spin b x +
        spin a y * spin b y + spin a z * spin b z := by
  unfold replicaBridgeInteraction
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp
  ring



theorem fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (w x y z : V) (s : Real) :
    fourBridgeAgreementSpinMass G J hf w x y z s =
      ghsiExp2 G J hf (fun a b =>
        if replicaBridgeInteraction (fourBridgeSites w x y z) a b = s
        then 1 else 0) := by
  rw [ghsiExp2_replicaBridgeFunction_eq_agreement G J hf
    (fourBridgeSites w x y z) (fun t => if t = s then 1 else 0)]
  unfold fourBridgeAgreementSpinMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : replicaAgreementSpin (fourBridgeSites w x y z) q = s
  · simp [hq]
  · simp [hq]

theorem ghsiExp2_sub
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (F H : ConfigSpace V -> ConfigSpace V -> Real) :
    ghsiExp2 G J hf (fun a b => F a b - H a b) =
      ghsiExp2 G J hf F - ghsiExp2 G J hf H := by
  rw [show (fun a b => F a b - H a b) =
      (fun a b => F a b + (-1 : Real) * H a b) by
    funext a b
    ring,
    ghsiExp2_add, ghsiExp2_const_mul]
  ring

theorem ghsiExp2_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) :
    ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
  have h := ghsiExp2_factor G J hf
    (fun _ => (1 : Real)) (fun _ => (1 : Real))
  simpa [expJ_one G J hf] using h

theorem fourBridge_agree_inter_eq_empty_iff (q : ConfigSpace V)
    (w x y z : V) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = ∅ ↔
      q w = false ∧ q x = false ∧ q y = false ∧ q z = false := by
  constructor
  · intro h
    have hn (v : V) (hv : v ∈ fourBridgeMarkedSet w x y z) : q v = false := by
      cases hq : q v
      · rfl
      · have hi : v ∈ ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z :=
          mem_inter.mpr ⟨(mem_ghsLAgreeFinset q v).mpr hq, hv⟩
        rw [h] at hi
        exact False.elim (by simpa using hi)
    exact ⟨hn w (by simp [fourBridgeMarkedSet]),
      hn x (by simp [fourBridgeMarkedSet]),
      hn y (by simp [fourBridgeMarkedSet]),
      hn z (by simp [fourBridgeMarkedSet])⟩
  · rintro ⟨hw, hx, hy, hz⟩
    ext v
    simp only [mem_inter, mem_ghsLAgreeFinset, Finset.notMem_empty,
      iff_false]
    rintro ⟨hq, hv⟩
    simp only [fourBridgeMarkedSet, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp_all

theorem fourBridge_agree_inter_eq_full_iff (q : ConfigSpace V)
    (w x y z : V) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z =
        fourBridgeMarkedSet w x y z ↔
      q w = true ∧ q x = true ∧ q y = true ∧ q z = true := by
  constructor
  · intro h
    have hp (v : V) (hv : v ∈ fourBridgeMarkedSet w x y z) : q v = true := by
      have hi : v ∈ ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z := by
        rw [h]
        exact hv
      exact (mem_ghsLAgreeFinset q v).mp (mem_inter.mp hi).1
    exact ⟨hp w (by simp [fourBridgeMarkedSet]),
      hp x (by simp [fourBridgeMarkedSet]),
      hp y (by simp [fourBridgeMarkedSet]),
      hp z (by simp [fourBridgeMarkedSet])⟩
  · rintro ⟨hw, hx, hy, hz⟩
    ext v
    simp only [mem_inter, mem_ghsLAgreeFinset]
    constructor
    · exact fun h => h.2
    · intro hv
      refine ⟨?_, hv⟩
      simp only [fourBridgeMarkedSet, mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp_all



theorem ghsLAgreeFinset_inter_eq_iff (q : ConfigSpace V)
    (M P : Finset V) :
    ghsLAgreeFinset q ∩ M = P ↔
      P ⊆ M ∧ ∀ v ∈ M, (q v = true ↔ v ∈ P) := by
  constructor
  · intro h
    constructor
    · intro v hvP
      have hi : v ∈ ghsLAgreeFinset q ∩ M := by
        rw [h]
        exact hvP
      exact (mem_inter.mp hi).2
    · intro v hvM
      constructor
      · intro hq
        have hi : v ∈ ghsLAgreeFinset q ∩ M :=
          mem_inter.mpr ⟨(mem_ghsLAgreeFinset q v).mpr hq, hvM⟩
        rwa [h] at hi
      · intro hvP
        have hi : v ∈ ghsLAgreeFinset q ∩ M := by
          rw [h]
          exact hvP
        exact (mem_ghsLAgreeFinset q v).mp (mem_inter.mp hi).1
  · rintro ⟨hPM, hcoord⟩
    ext v
    simp only [mem_inter, mem_ghsLAgreeFinset]
    constructor
    · rintro ⟨hq, hvM⟩
      exact (hcoord v hvM).mp hq
    · intro hvP
      have hvM := hPM hvP
      exact ⟨(hcoord v hvM).mpr hvP, hvM⟩

theorem fourBridge_agree_inter_eq_singleton_w_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {w} ↔
      q w = true ∧ q x = false ∧ q y = false ∧ q z = false := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_singleton_x_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {x} ↔
      q w = false ∧ q x = true ∧ q y = false ∧ q z = false := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_singleton_y_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {y} ↔
      q w = false ∧ q x = false ∧ q y = true ∧ q z = false := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_singleton_z_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {z} ↔
      q w = false ∧ q x = false ∧ q y = false ∧ q z = true := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_cosingleton_w_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z =
        fourBridgeMarkedSet w x y z \ {w} ↔
      q w = false ∧ q x = true ∧ q y = true ∧ q z = true := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_cosingleton_x_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z =
        fourBridgeMarkedSet w x y z \ {x} ↔
      q w = true ∧ q x = false ∧ q y = true ∧ q z = true := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_cosingleton_y_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z =
        fourBridgeMarkedSet w x y z \ {y} ↔
      q w = true ∧ q x = true ∧ q y = false ∧ q z = true := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]

theorem fourBridge_agree_inter_eq_cosingleton_z_iff (q : ConfigSpace V)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z =
        fourBridgeMarkedSet w x y z \ {z} ↔
      q w = true ∧ q x = true ∧ q y = true ∧ q z = false := by
  rw [ghsLAgreeFinset_inter_eq_iff]
  simp [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
    hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]


theorem fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z (-4) =
      ghsiAgreementMarginalProb G J hf
        (fourBridgeMarkedSet w x y z) ∅ := by
  classical
  unfold fourBridgeAgreementSpinMass ghsiAgreementMarginalProb
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  rw [replicaAgreementSpin_fourBridgeSites]
  rw [fourBridge_agree_inter_eq_empty_iff]
  cases hw : q w <;> cases hx : q x <;> cases hy : q y <;>
    cases hz : q z <;>
    norm_num [spin, hw, hx, hy, hz]


theorem fourBridgeAgreementSpinMass_four_eq_marginal_full
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z 4 =
      ghsiAgreementMarginalProb G J hf
        (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z) := by
  classical
  unfold fourBridgeAgreementSpinMass ghsiAgreementMarginalProb
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  rw [replicaAgreementSpin_fourBridgeSites]
  rw [fourBridge_agree_inter_eq_full_iff]
  cases hw : q w <;> cases hx : q x <;> cases hy : q y <;>
    cases hz : q z <;>
    norm_num [spin, hw, hx, hy, hz]


theorem fourBridgeAgreementSpinMass_neg_two_eq_marginal_singletons
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeAgreementSpinMass G J hf w x y z (-2) =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {z} := by
  classical
  unfold fourBridgeAgreementSpinMass ghsiAgreementMarginalProb
  simp_rw [Finset.sum_filter]
  repeat' rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [replicaAgreementSpin_fourBridgeSites]
  cases hw : q w <;> cases hx : q x <;> cases hy : q y <;>
    cases hz : q z <;>
    norm_num [spin, fourBridge_agree_inter_eq_singleton_w_iff,
      fourBridge_agree_inter_eq_singleton_x_iff,
      fourBridge_agree_inter_eq_singleton_y_iff,
      fourBridge_agree_inter_eq_singleton_z_iff, hw, hx, hy, hz,
      hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm, hwz.symm,
      hxy.symm, hxz.symm, hyz.symm]


theorem fourBridgeAgreementSpinMass_two_eq_marginal_cosingletons
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeAgreementSpinMass G J hf w x y z 2 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {w}) +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {x}) +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {y}) +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {z}) := by
  classical
  unfold fourBridgeAgreementSpinMass ghsiAgreementMarginalProb
  simp_rw [Finset.sum_filter]
  repeat' rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [replicaAgreementSpin_fourBridgeSites]
  cases hw : q w <;> cases hx : q x <;> cases hy : q y <;>
    cases hz : q z <;>
    norm_num [spin, fourBridge_agree_inter_eq_cosingleton_w_iff,
      fourBridge_agree_inter_eq_cosingleton_x_iff,
      fourBridge_agree_inter_eq_cosingleton_y_iff,
      fourBridge_agree_inter_eq_cosingleton_z_iff, hw, hx, hy, hz,
      hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm, hwz.symm,
      hxy.symm, hxz.symm, hyz.symm]


theorem fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z (-4) =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 0 := by
  rw [fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator]
  have hindicator :
      (fun a b : ConfigSpace V =>
        if replicaBridgeInteraction (fourBridgeSites w x y z) a b = (-4 : Real)
        then 1 else 0) =
      (fun a b =>
        ((1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
          (1 - spin a y * spin b y) * (1 - spin a z * spin b z)) / 16) := by
    funext a b
    have hpm (v : V) :
        spin a v * spin b v = 1 ∨ spin a v * spin b v = -1 := by
      rcases spin_eq_pm a v with ha | ha <;>
        rcases spin_eq_pm b v with hb | hb <;> simp [ha, hb]
    rcases hpm w with hw | hw <;> rcases hpm x with hx | hx <;>
      rcases hpm y with hy | hy <;> rcases hpm z with hz | hz <;>
      rw [replicaBridgeInteraction_fourBridgeSites] <;>
      simp [hw, hx, hy, hz] <;> norm_num
  rw [hindicator]
  have hfourier :
      (fun a b : ConfigSpace V =>
        ((1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
          (1 - spin a y * spin b y) * (1 - spin a z * spin b z)) / 16) =
      (fun a b => (1 / 16 : Real) *
        ((1 : Real) +
          (-1) * (spin a w * spin b w) +
          (-1) * (spin a x * spin b x) +
          (-1) * (spin a y * spin b y) +
          (-1) * (spin a z * spin b z) +
          (spin a w * spin a x) * (spin b w * spin b x) +
          (spin a w * spin a y) * (spin b w * spin b y) +
          (spin a w * spin a z) * (spin b w * spin b z) +
          (spin a x * spin a y) * (spin b x * spin b y) +
          (spin a x * spin a z) * (spin b x * spin b z) +
          (spin a y * spin a z) * (spin b y * spin b z) +
          (-1) * ((spin a w * (spin a x * spin a y)) *
            (spin b w * (spin b x * spin b y))) +
          (-1) * ((spin a w * (spin a x * spin a z)) *
            (spin b w * (spin b x * spin b z))) +
          (-1) * ((spin a w * (spin a y * spin a z)) *
            (spin b w * (spin b y * spin b z))) +
          (-1) * ((spin a x * (spin a y * spin a z)) *
            (spin b x * (spin b y * spin b z))) +
          (spin a w * (spin a x * (spin a y * spin a z))) *
            (spin b w * (spin b x * (spin b y * spin b z))))) := by
    funext a b
    ring
  rw [hfourier]
  simp only [ghsiExp2_const_mul, ghsiExp2_add, ghsiExp2_factor]
  rw [ghsiExp2_one]
  simp only [fourBridgeRankMass]
  dsimp [fourBridgeOneCoeff, fourBridgeTwoCoeff,
    fourBridgeThreeCoeff, fourBridgeFourCoeff]
  ring


theorem fourBridgeAgreementSpinMass_four_eq_rankMass_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z 4 =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 4 := by
  rw [fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator]
  have hindicator :
      (fun a b : ConfigSpace V =>
        if replicaBridgeInteraction (fourBridgeSites w x y z) a b = (4 : Real)
        then 1 else 0) =
      (fun a b =>
        ((1 + spin a w * spin b w) * (1 + spin a x * spin b x) *
          (1 + spin a y * spin b y) * (1 + spin a z * spin b z)) / 16) := by
    funext a b
    have hpm (v : V) :
        spin a v * spin b v = 1 ∨ spin a v * spin b v = -1 := by
      rcases spin_eq_pm a v with ha | ha <;>
        rcases spin_eq_pm b v with hb | hb <;> simp [ha, hb]
    rcases hpm w with hw | hw <;> rcases hpm x with hx | hx <;>
      rcases hpm y with hy | hy <;> rcases hpm z with hz | hz <;>
      rw [replicaBridgeInteraction_fourBridgeSites] <;>
      simp [hw, hx, hy, hz] <;> norm_num
  rw [hindicator]
  have hfourier :
      (fun a b : ConfigSpace V =>
        ((1 + spin a w * spin b w) * (1 + spin a x * spin b x) *
          (1 + spin a y * spin b y) * (1 + spin a z * spin b z)) / 16) =
      (fun a b => (1 / 16 : Real) *
        ((1 : Real) +
          spin a w * spin b w + spin a x * spin b x +
          spin a y * spin b y + spin a z * spin b z +
          (spin a w * spin a x) * (spin b w * spin b x) +
          (spin a w * spin a y) * (spin b w * spin b y) +
          (spin a w * spin a z) * (spin b w * spin b z) +
          (spin a x * spin a y) * (spin b x * spin b y) +
          (spin a x * spin a z) * (spin b x * spin b z) +
          (spin a y * spin a z) * (spin b y * spin b z) +
          (spin a w * (spin a x * spin a y)) *
            (spin b w * (spin b x * spin b y)) +
          (spin a w * (spin a x * spin a z)) *
            (spin b w * (spin b x * spin b z)) +
          (spin a w * (spin a y * spin a z)) *
            (spin b w * (spin b y * spin b z)) +
          (spin a x * (spin a y * spin a z)) *
            (spin b x * (spin b y * spin b z)) +
          (spin a w * (spin a x * (spin a y * spin a z))) *
            (spin b w * (spin b x * (spin b y * spin b z))))) := by
    funext a b
    ring
  rw [hfourier]
  simp only [ghsiExp2_const_mul, ghsiExp2_add, ghsiExp2_factor]
  rw [ghsiExp2_one]
  simp only [fourBridgeRankMass]
  dsimp [fourBridgeOneCoeff, fourBridgeTwoCoeff,
    fourBridgeThreeCoeff, fourBridgeFourCoeff]
  ring

private theorem ghsiExp2_fourBridge_rankFourier
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V)
    (c0 c1 c3 c4 : Real) :
    ghsiExp2 G J hf (fun a b => (1 / 16 : Real) *
      (c0 + c1 * (spin a w * spin b w + spin a x * spin b x +
          spin a y * spin b y + spin a z * spin b z) +
        c3 * ((spin a w * (spin a x * spin a y)) *
              (spin b w * (spin b x * spin b y)) +
            (spin a w * (spin a x * spin a z)) *
              (spin b w * (spin b x * spin b z)) +
            (spin a w * (spin a y * spin a z)) *
              (spin b w * (spin b y * spin b z)) +
            (spin a x * (spin a y * spin a z)) *
              (spin b x * (spin b y * spin b z))) +
        c4 * ((spin a w * (spin a x * (spin a y * spin a z))) *
          (spin b w * (spin b x * (spin b y * spin b z)))))) =
      (c0 + c1 * fourBridgeOneCoeff G J hf w x y z +
        c3 * fourBridgeThreeCoeff G J hf w x y z +
        c4 * fourBridgeFourCoeff G J hf w x y z) / 16 := by
  have hconst :
      ghsiExp2 G J hf (fun _ _ : ConfigSpace V => c0) = c0 := by
    have h := ghsiExp2_const_mul (G := G) J hf c0
      (fun _ _ : ConfigSpace V => (1 : Real))
    rw [ghsiExp2_one] at h
    simpa using h
  simp only [ghsiExp2_const_mul, ghsiExp2_add, ghsiExp2_factor]
  rw [hconst]
  dsimp [fourBridgeOneCoeff, fourBridgeThreeCoeff,
    fourBridgeFourCoeff]
  ring


theorem fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z (-2) =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 1 := by
  rw [fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator]
  have hindicator :
      (fun a b : ConfigSpace V =>
        if replicaBridgeInteraction (fourBridgeSites w x y z) a b = (-2 : Real)
        then 1 else 0) =
      (fun a b =>
        ((1 + spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 - spin a z * spin b z) +
          (1 - spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 - spin a z * spin b z) +
          (1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 - spin a z * spin b z) +
          (1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 + spin a z * spin b z)) / 16) := by
    funext a b
    have hpm (v : V) :
        spin a v * spin b v = 1 ∨ spin a v * spin b v = -1 := by
      rcases spin_eq_pm a v with ha | ha <;>
        rcases spin_eq_pm b v with hb | hb <;> simp [ha, hb]
    rcases hpm w with hw | hw <;> rcases hpm x with hx | hx <;>
      rcases hpm y with hy | hy <;> rcases hpm z with hz | hz <;>
      rw [replicaBridgeInteraction_fourBridgeSites] <;>
      simp [hw, hx, hy, hz] <;> norm_num
  rw [hindicator]
  have hfourier :
      (fun a b : ConfigSpace V =>
        ((1 + spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 - spin a z * spin b z) +
          (1 - spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 - spin a z * spin b z) +
          (1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 - spin a z * spin b z) +
          (1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 + spin a z * spin b z)) / 16) =
      (fun a b => (1 / 16 : Real) *
        (4 * (1 : Real) + (-2) * (spin a w * spin b w + spin a x * spin b x +
            spin a y * spin b y + spin a z * spin b z) +
          2 * ((spin a w * (spin a x * spin a y)) *
                (spin b w * (spin b x * spin b y)) +
              (spin a w * (spin a x * spin a z)) *
                (spin b w * (spin b x * spin b z)) +
              (spin a w * (spin a y * spin a z)) *
                (spin b w * (spin b y * spin b z)) +
              (spin a x * (spin a y * spin a z)) *
                (spin b x * (spin b y * spin b z))) +
          (-4) * ((spin a w * (spin a x * (spin a y * spin a z))) *
            (spin b w * (spin b x * (spin b y * spin b z)))))) := by
    funext a b
    ring
  rw [hfourier, ghsiExp2_fourBridge_rankFourier]
  simp only [fourBridgeRankMass]
  ring


theorem fourBridgeAgreementSpinMass_two_eq_rankMass_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z 2 =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 3 := by
  rw [fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator]
  have hindicator :
      (fun a b : ConfigSpace V =>
        if replicaBridgeInteraction (fourBridgeSites w x y z) a b = (2 : Real)
        then 1 else 0) =
      (fun a b =>
        ((1 - spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 + spin a z * spin b z) +
          (1 + spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 + spin a z * spin b z) +
          (1 + spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 + spin a z * spin b z) +
          (1 + spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 - spin a z * spin b z)) / 16) := by
    funext a b
    have hpm (v : V) :
        spin a v * spin b v = 1 ∨ spin a v * spin b v = -1 := by
      rcases spin_eq_pm a v with ha | ha <;>
        rcases spin_eq_pm b v with hb | hb <;> simp [ha, hb]
    rcases hpm w with hw | hw <;> rcases hpm x with hx | hx <;>
      rcases hpm y with hy | hy <;> rcases hpm z with hz | hz <;>
      rw [replicaBridgeInteraction_fourBridgeSites] <;>
      simp [hw, hx, hy, hz] <;> norm_num
  rw [hindicator]
  have hfourier :
      (fun a b : ConfigSpace V =>
        ((1 - spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 + spin a z * spin b z) +
          (1 + spin a w * spin b w) * (1 - spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 + spin a z * spin b z) +
          (1 + spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 - spin a y * spin b y) * (1 + spin a z * spin b z) +
          (1 + spin a w * spin b w) * (1 + spin a x * spin b x) *
            (1 + spin a y * spin b y) * (1 - spin a z * spin b z)) / 16) =
      (fun a b => (1 / 16 : Real) *
        (4 * (1 : Real) + 2 * (spin a w * spin b w + spin a x * spin b x +
            spin a y * spin b y + spin a z * spin b z) +
          (-2) * ((spin a w * (spin a x * spin a y)) *
                (spin b w * (spin b x * spin b y)) +
              (spin a w * (spin a x * spin a z)) *
                (spin b w * (spin b x * spin b z)) +
              (spin a w * (spin a y * spin a z)) *
                (spin b w * (spin b y * spin b z)) +
              (spin a x * (spin a y * spin a z)) *
                (spin b x * (spin b y * spin b z))) +
          (-4) * ((spin a w * (spin a x * (spin a y * spin a z))) *
            (spin b w * (spin b x * (spin b y * spin b z)))))) := by
    funext a b
    ring
  rw [hfourier, ghsiExp2_fourBridge_rankFourier]
  simp only [fourBridgeRankMass]
  ring



theorem fourBridgeRankMass_rankCross
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 0 *
        fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 3 ≤
      fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 1 *
        fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 4 := by
  classical
  let M := fourBridgeMarkedSet w x y z
  let C : Real := (4 * Fintype.card (ConfigSpace V) : Real) *
    (ZJ G.edgeFinset J hf) ^ 2
  have hC : 0 < C := by
    have hcard : 0 < Fintype.card (ConfigSpace V) := Fintype.card_pos
    have hZ : 0 < ZJ G.edgeFinset J hf := ZJ_pos _ _ _
    dsimp [C]
    positivity
  have hzero : ghsiSubsetMarginalMass G J hf M ∅ =
      C * fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 0 := by
    rw [ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G J hf (M := M) (P := ∅) (empty_subset _)]
    rw [← fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty
      G J hf w x y z]
    rw [fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero]
  have hfour : ghsiSubsetMarginalMass G J hf M M =
      C * fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 4 := by
    rw [ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G J hf (M := M) (P := M) (Subset.rfl)]
    rw [← fourBridgeAgreementSpinMass_four_eq_marginal_full
      G J hf w x y z]
    rw [fourBridgeAgreementSpinMass_four_eq_rankMass_four]
  have hsingle (v : V) (hv : v ∈ M) :
      ghsiSubsetMarginalMass G J hf M {v} =
        C * ghsiAgreementMarginalProb G J hf M {v} := by
    simpa [C] using
      ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
        G J hf (M := M) (P := {v}) (singleton_subset_iff.mpr hv)
  have hcosingle (v : V) :
      ghsiSubsetMarginalMass G J hf M (M \ {v}) =
        C * ghsiAgreementMarginalProb G J hf M (M \ {v}) := by
    simpa [C] using
      ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
        G J hf (M := M) (P := M \ {v}) sdiff_subset
  have hone : (∑ v ∈ M, ghsiSubsetMarginalMass G J hf M {v}) =
      C * fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 1 := by
    have hwM : w ∈ M := by simp [M, fourBridgeMarkedSet]
    have hxM : x ∈ M := by simp [M, fourBridgeMarkedSet]
    have hyM : y ∈ M := by simp [M, fourBridgeMarkedSet]
    have hzM : z ∈ M := by simp [M, fourBridgeMarkedSet]
    rw [show (∑ v ∈ M, ghsiSubsetMarginalMass G J hf M {v}) =
        ghsiSubsetMarginalMass G J hf M {w} +
        ghsiSubsetMarginalMass G J hf M {x} +
        ghsiSubsetMarginalMass G J hf M {y} +
        ghsiSubsetMarginalMass G J hf M {z} by
      dsimp [M, fourBridgeMarkedSet]
      simp [hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm,
        hwz.symm, hxy.symm, hxz.symm, hyz.symm]
      ring]
    rw [hsingle w hwM, hsingle x hxM, hsingle y hyM, hsingle z hzM]
    rw [← mul_add, ← mul_add, ← mul_add]
    rw [← fourBridgeAgreementSpinMass_neg_two_eq_marginal_singletons
      G J hf hwx hwy hwz hxy hxz hyz]
    rw [fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one]
  have hthree :
      (∑ v ∈ M, ghsiSubsetMarginalMass G J hf M (M \ {v})) =
      C * fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 3 := by
    rw [show (∑ v ∈ M,
        ghsiSubsetMarginalMass G J hf M (M \ {v})) =
        ghsiSubsetMarginalMass G J hf M (M \ {w}) +
        ghsiSubsetMarginalMass G J hf M (M \ {x}) +
        ghsiSubsetMarginalMass G J hf M (M \ {y}) +
        ghsiSubsetMarginalMass G J hf M (M \ {z}) by
      dsimp [M, fourBridgeMarkedSet]
      simp [hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm,
        hwz.symm, hxy.symm, hxz.symm, hyz.symm]
      ring]
    rw [hcosingle w, hcosingle x, hcosingle y, hcosingle z]
    rw [← mul_add, ← mul_add, ← mul_add]
    rw [← fourBridgeAgreementSpinMass_two_eq_marginal_cosingletons
      G J hf hwx hwy hwz hxy hxz hyz]
    rw [fourBridgeAgreementSpinMass_two_eq_rankMass_three]
  have hraw := ghsiSubsetMarginalMass_rank_zero_three_le_one_four
    G J hf hJ hhf M
  rw [hzero, hthree, hone, hfour] at hraw
  nlinarith [sq_pos_of_pos hC]




theorem fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 5 ≤ 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 6 ≤ 0 := by
  apply fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos_of_rankCross
  exact fourBridgeRankMass_rankCross G J hf hJ hhf
    hwx hwy hwz hxy hxz hyz

end

end StatMech.Ising
