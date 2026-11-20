/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardLocalAngularSplit
import Code.FrontierA.TriangularIsingTorusAngularSplit
import Code.FrontierA.TriangularIsingTorusCycleHolonomy









namespace StatMech.FrontierA

open SimpleGraph



def triangularTorusDirectionRank : Fin 6 -> Fin 6 :=
  ![5, 2, 1, 4, 0, 3]


def triangularTorusDirectionRankEquiv : Equiv.Perm (Fin 6) where
  toFun := triangularTorusDirectionRank
  invFun := ![4, 2, 1, 5, 3, 0]
  left_inv a := by
    fin_cases a <;> rfl
  right_inv a := by
    fin_cases a <;> rfl



noncomputable def triangularTorusOutgoingDirectionEquiv
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    KWOutgoingDart (G := triangularTorusGraph L) v ≃ Fin 6 where
  toFun d := triangularTorusGraphDartDirection L d.1
  invFun a := ⟨triangularTorusDartEquiv L (v, a), rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply (triangularTorusDartEquiv L).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Prod.ext
    · have h := congrArg (fun z : (triangularTorusGraph L).Dart => z.fst)
        ((triangularTorusDartEquiv L).apply_symm_apply d.1)
      exact (h.trans d.2).symm
    · rfl
  right_inv a := by
    change ((triangularTorusDartEquiv L).symm
      (triangularTorusDartEquiv L (v, a))).2 = a
    rw [Equiv.symm_apply_apply]

theorem triangularTorusOutgoingDart_card
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    Fintype.card (KWOutgoingDart (G := triangularTorusGraph L) v) = 6 := by
  simpa using Fintype.card_congr (triangularTorusOutgoingDirectionEquiv L v)



noncomputable def triangularTorusLocalPortOrder
    (L : Nat) [Fact (2 < L)] : KWPortOrder (triangularTorusGraph L) :=
  fun v =>
    (Fintype.equivFin
      (KWOutgoingDart (G := triangularTorusGraph L) v)).symm |>.trans
      ((triangularTorusOutgoingDirectionEquiv L v).trans
        triangularTorusDirectionRankEquiv) |>.trans
      (Fin.castOrderIso (triangularTorusOutgoingDart_card L v).symm).toEquiv

theorem triangularTorusLocalPortOrder_rank
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    kwOrderedPortRank (triangularTorusLocalPortOrder L) p =
      (triangularTorusDirectionRank
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) p))).val := by
  rcases p with ⟨v, i⟩
  unfold kwOrderedPortRank triangularTorusLocalPortOrder
    triangularTorusDirectionRankEquiv
  change (((Fin.castOrderIso
    (triangularTorusOutgoingDart_card L v).symm)
      (triangularTorusDirectionRank
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) ⟨v, i⟩)))).val) = _
  simp


def triangularTorusDirectionSignedAngle : Fin 6 -> Int :=
  ![4, 0, -2, 2, -3, 1]


noncomputable def triangularTorusLocalPortRoot
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (p : KWDartPort (triangularTorusGraph L)) : Complex :=
  rho ^ triangularTorusDirectionSignedAngle
    (triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) p))

theorem triangularTorusGraphDartDirection_symm
    (L : Nat) [Fact (2 < L)]
    (d : (triangularTorusGraph L).Dart) :
    triangularTorusGraphDartDirection L d.symm =
      triangularTorusDirectionReverse
        (triangularTorusGraphDartDirection L d) := by
  let a := (triangularTorusDartEquiv L).symm d
  have hd : triangularTorusDartEquiv L a = d :=
    (triangularTorusDartEquiv L).apply_symm_apply d
  unfold triangularTorusGraphDartDirection
  rw [← hd, ← triangularTorusDartEquiv_reverse]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl



theorem triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (a b : Fin 6)
    (hrank : (triangularTorusDirectionRank
        (triangularTorusDirectionReverse a)).val <
      (triangularTorusDirectionRank b).val) :
    triangularKacWardTurnMatrix rho a b =
      -Complex.I *
        (rho ^ triangularTorusDirectionSignedAngle
          (triangularTorusDirectionReverse a))⁻¹ *
        rho ^ triangularTorusDirectionSignedAngle b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hrank ⊢ <;>
    field_simp <;>
    simp [hrho]


theorem triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (a b : Fin 6)
    (hrank : (triangularTorusDirectionRank b).val <
      (triangularTorusDirectionRank
        (triangularTorusDirectionReverse a)).val) :
    triangularKacWardTurnMatrix rho a b =
      Complex.I *
        (rho ^ triangularTorusDirectionSignedAngle
          (triangularTorusDirectionReverse a))⁻¹ *
        rho ^ triangularTorusDirectionSignedAngle b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hrank ⊢ <;>
    field_simp <;>
    simp [hrho, hrho12]


noncomputable def triangularTorusLocalAngularData
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    KWLocalAngularData (triangularTorusGraph L) where
  order := triangularTorusLocalPortOrder L
  root := triangularTorusLocalPortRoot L rho
  phase := triangularTorusGraphPhase L rho 1 1
  phase_eq_portRoots_of_rank_lt d e _hde hrank := by
    rw [triangularTorusGraphPhase_one_one_apply]
    unfold triangularTorusLocalPortRoot
    simp only [kwDartOfPort_portOfDart]
    rw [triangularTorusGraphDartDirection_symm]
    apply triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt rho hrho
    rw [triangularTorusLocalPortOrder_rank,
      triangularTorusLocalPortOrder_rank] at hrank
    simp only [kwDartOfPort_portOfDart,
      triangularTorusGraphDartDirection_symm] at hrank
    exact hrank
  phase_eq_portRoots_of_rank_gt d e _hde hrank := by
    rw [triangularTorusGraphPhase_one_one_apply]
    unfold triangularTorusLocalPortRoot
    simp only [kwDartOfPort_portOfDart]
    rw [triangularTorusGraphDartDirection_symm]
    apply triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt rho hrho
    rw [triangularTorusLocalPortOrder_rank,
      triangularTorusLocalPortOrder_rank] at hrank
    simp only [kwDartOfPort_portOfDart,
      triangularTorusGraphDartDirection_symm] at hrank
    exact hrank
  root_ne_zero p := by
    unfold triangularTorusLocalPortRoot
    exact zpow_ne_zero _ (triangularTorusTurnRoot_ne_zero rho hrho)
  root_sq_symm d := by
    unfold triangularTorusLocalPortRoot
    simp only [kwDartOfPort_portOfDart,
      triangularTorusGraphDartDirection_symm]
    have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
    have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
    generalize triangularTorusGraphDartDirection L d = a
    fin_cases a <;>
      simp [triangularTorusDirectionReverse,
        triangularTorusDirectionSignedAngle] <;>
      field_simp <;>
      simp [hrho, hrho8]



theorem triangularTorus_localAngularSplit_det_eq_original
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L))
      (kwOrderedSplitWeight (triangularTorusGraph L) weight)
      (kwLocalAngularSplitPhase
        (triangularTorusLocalAngularData L rho hrho))).det =
      (1 - kwGraphTransition (triangularTorusGraph L) weight
        (triangularTorusGraphPhase L rho 1 1)).det := by
  exact kwLocalAngularSplit_det_eq_original
    (triangularTorusLocalAngularData L rho hrho) weight

end StatMech.FrontierA
