/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy
import Code.FrontierA.IsingSurfaceTensionSheetGauge

namespace StatMech.FrontierA

open scoped BigOperators symmDiff
open Filter Topology
open StatMech StatMech.Ising

noncomputable section


def oddCubicalCellEquivPrismSite (n : Nat) :
    CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1) ≃
      RectangularPrismSite (2 * n + 1) (2 * n + 1) n where
  toFun q := ⟨q.x, q.y, q.z⟩
  invFun v := ⟨v.x, v.y, v.z⟩
  left_inv q := by cases q; rfl
  right_inv v := by cases v; rfl



def oddCubicalAnchoredEquivPrismConfig (n : Nat) :
    AnchoredConfig
        (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none ≃
      RectangularPrismConfig (2 * n + 1) (2 * n + 1) n where
  toFun s v := !s.1 (some ((oddCubicalCellEquivPrismSite n).symm v))
  invFun sigma := ⟨fun q => match q with
    | none => false
    | some v => !sigma (oddCubicalCellEquivPrismSite n v), rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext q
    cases q with
    | none => exact s.2.symm
    | some q => simp
  right_inv sigma := by
    funext v
    simp

@[simp] theorem oddCubicalCellEquivPrismSite_symm_apply
    (n : Nat) (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (oddCubicalCellEquivPrismSite n).symm v = ⟨v.x, v.y, v.z⟩ := rfl



def cubicalPlaquetteToOddPrism (n : Nat) :
    CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) ->
      OddPrismTouchIndex n
  | .xy x y z =>
      if hz0 : z.val = 0 then .zZero x y
      else if hz1 : z.val = 2 * n + 1 then .zLast x y
      else .zInternal x y ⟨z.val - 1, by omega⟩
  | .xz x y z =>
      if hy0 : y.val = 0 then .yZero x z
      else if hy1 : y.val = 2 * n + 1 then .yLast x z
      else .yInternal x ⟨y.val - 1, by omega⟩ z
  | .yz x y z =>
      if hx0 : x.val = 0 then .xZero y z
      else if hx1 : x.val = 2 * n + 1 then .xLast y z
      else .xInternal ⟨x.val - 1, by omega⟩ y z

def oddPrismToCubicalPlaquette (n : Nat) :
    OddPrismTouchIndex n ->
      CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1)
  | .xInternal x y z => .yz ⟨x.val + 1, by omega⟩ y z
  | .yInternal x y z => .xz x ⟨y.val + 1, by omega⟩ z
  | .zInternal x y z => .xy x y ⟨z.val + 1, by omega⟩
  | .xZero y z => .yz 0 y z
  | .xLast y z => .yz (Fin.last (2 * n + 1)) y z
  | .yZero x z => .xz x 0 z
  | .yLast x z => .xz x (Fin.last (2 * n + 1)) z
  | .zZero x y => .xy x y 0
  | .zLast x y => .xy x y (Fin.last (2 * n + 1))

theorem cubicalPlaquetteToOddPrism_leftInverse (n : Nat) :
    Function.LeftInverse (oddPrismToCubicalPlaquette n)
      (cubicalPlaquetteToOddPrism n) := by
  intro p
  cases p with
  | xy x y z =>
      simp only [cubicalPlaquetteToOddPrism]
      split_ifs with hz0 hz1
      · apply congrArg (CubicalPlaquette.xy x y)
        apply Fin.ext
        simp [hz0]
      · apply congrArg (CubicalPlaquette.xy x y)
        apply Fin.ext
        simp [Fin.last, hz1]
      · apply congrArg (CubicalPlaquette.xy x y)
        apply Fin.ext
        simp
        omega
  | xz x y z =>
      simp only [cubicalPlaquetteToOddPrism]
      split_ifs with hy0 hy1
      · apply congrArg (fun y => CubicalPlaquette.xz x y z)
        apply Fin.ext
        simp [hy0]
      · apply congrArg (fun y => CubicalPlaquette.xz x y z)
        apply Fin.ext
        simp [Fin.last, hy1]
      · apply congrArg (fun y => CubicalPlaquette.xz x y z)
        apply Fin.ext
        simp
        omega
  | yz x y z =>
      simp only [cubicalPlaquetteToOddPrism]
      split_ifs with hx0 hx1
      · apply congrArg (fun x => CubicalPlaquette.yz x y z)
        apply Fin.ext
        simp [hx0]
      · apply congrArg (fun x => CubicalPlaquette.yz x y z)
        apply Fin.ext
        simp [Fin.last, hx1]
      · apply congrArg (fun x => CubicalPlaquette.yz x y z)
        apply Fin.ext
        simp
        omega

theorem cubicalPlaquetteToOddPrism_rightInverse (n : Nat) :
    Function.RightInverse (oddPrismToCubicalPlaquette n)
      (cubicalPlaquetteToOddPrism n) := by
  intro q
  cases q <;>
    simp [oddPrismToCubicalPlaquette, cubicalPlaquetteToOddPrism,
      Fin.last] <;>
    omega

def oddCubicalPlaquetteEquivOddPrismTouchIndex (n : Nat) :
    CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) ≃
      OddPrismTouchIndex n where
  toFun := cubicalPlaquetteToOddPrism n
  invFun := oddPrismToCubicalPlaquette n
  left_inv := cubicalPlaquetteToOddPrism_leftInverse n
  right_inv := cubicalPlaquetteToOddPrism_rightInverse n

@[simp] theorem finBackward_oddInternalFace (n : Nat) (k : Fin (2 * n)) :
    finBackward (⟨k.val + 1, by omega⟩ : Fin (2 * n + 2)) =
      some (⟨k.val, by omega⟩ : Fin (2 * n + 1)) := by
  rw [finBackward_eq_some_iff]
  apply Fin.ext
  simp

@[simp] theorem finForward_oddInternalFace (n : Nat) (k : Fin (2 * n)) :
    finForward (⟨k.val + 1, by omega⟩ : Fin (2 * n + 2)) =
      some (⟨k.val + 1, by omega⟩ : Fin (2 * n + 1)) := by
  rw [finForward_eq_some_iff]
  apply Fin.ext
  simp

@[simp] theorem finBackward_oddZeroFace (n : Nat) :
    finBackward (0 : Fin (2 * n + 2)) =
      (none : Option (Fin (2 * n + 1))) := by
  rfl

@[simp] theorem finForward_oddZeroFace (n : Nat) :
    finForward (0 : Fin (2 * n + 2)) =
      some (0 : Fin (2 * n + 1)) := by
  rw [finForward_eq_some_iff]
  apply Fin.ext
  simp

@[simp] theorem finBackward_oddLastFace (n : Nat) :
    finBackward (Fin.last (2 * n + 1) : Fin (2 * n + 2)) =
      some (Fin.last (2 * n) : Fin (2 * n + 1)) := by
  rw [finBackward_eq_some_iff]
  apply Fin.ext
  simp [Fin.last]

@[simp] theorem finForward_oddLastFace (n : Nat) :
    finForward (Fin.last (2 * n + 1) : Fin (2 * n + 2)) =
      (none : Option (Fin (2 * n + 1))) := by
  simp [finForward]

theorem boolAgreement_eq_spin_not_mul (a b : Bool) :
    (if a = b then (1 : Real) else -1) =
      (if !a then (1 : Real) else -1) *
        (if !b then (1 : Real) else -1) := by
  cases a <;> cases b <;> norm_num

theorem boolFalseAgreement_eq_spin_not (a : Bool) :
    (if false = a then (1 : Real) else -1) =
      (if !a then (1 : Real) else -1) := by
  cases a <;> norm_num

theorem boolAgreementFalse_eq_spin_not (a : Bool) :
    (if a = false then (1 : Real) else -1) =
      (if !a then (1 : Real) else -1) := by
  cases a <;> norm_num



theorem oddCubicalDualAgreement_eq_plusInteraction
    (n : Nat)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none)
    (q : OddPrismTouchIndex n) :
    (if s.1 (cubicalDualEnds (oddPrismToCubicalPlaquette n q)).1 =
          s.1 (cubicalDualEnds (oddPrismToCubicalPlaquette n q)).2
      then (1 : Real) else -1) =
      oddPrismPlusInteractionTerm n
        (oddCubicalAnchoredEquivPrismConfig n s) q := by
  cases q <;>
    simp only [oddPrismToCubicalPlaquette, cubicalDualEnds,
      oddCubicalAnchoredEquivPrismConfig, oddCubicalCellEquivPrismSite,
      oddPrismPlusInteractionTerm, rectangularPrismSpin, spin, s.2,
      finBackward_oddInternalFace, finForward_oddInternalFace,
      finBackward_oddZeroFace, finForward_oddZeroFace,
      finBackward_oddLastFace, finForward_oddLastFace,
      Option.map_some, Option.map_none, Equiv.coe_fn_mk]
  all_goals first
    | exact boolAgreement_eq_spin_not_mul _ _
    | exact boolFalseAgreement_eq_spin_not _
    | exact boolAgreementFalse_eq_spin_not _



theorem sum_oddCubicalDualAgreement_eq_plusPrismInteraction
    (J beta : Real) (n : Nat)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none) :
    (∑ p : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1),
        beta * J *
          (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2
            then (1 : Real) else -1)) =
      beta * J *
        (rectangularPrismInternalInteraction
            (oddCubicalAnchoredEquivPrismConfig n s) +
          rectangularPrismPlusBoundaryInteraction
            (oddCubicalAnchoredEquivPrismConfig n s)) := by
  calc
    (∑ p : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1),
        beta * J *
          (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2
            then (1 : Real) else -1)) =
        ∑ q : OddPrismTouchIndex n, beta * J *
          (if s.1 (cubicalDualEnds (oddPrismToCubicalPlaquette n q)).1 =
              s.1 (cubicalDualEnds (oddPrismToCubicalPlaquette n q)).2
            then (1 : Real) else -1) := by
      symm
      exact Equiv.sum_comp
        (oddCubicalPlaquetteEquivOddPrismTouchIndex n).symm
        (fun p : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) =>
          beta * J *
            (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2
              then (1 : Real) else -1))
    _ = ∑ q : OddPrismTouchIndex n, beta * J *
        oddPrismPlusInteractionTerm n
          (oddCubicalAnchoredEquivPrismConfig n s) q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [oddCubicalDualAgreement_eq_plusInteraction]
    _ = _ := by
      rw [← Finset.mul_sum, sum_oddPrismPlusInteractionTerm,
        rectangularPrismPlusBoundaryInteraction_eq_faces]



theorem oddCubicalDualPartition_eq_two_mul_plusPrismPartition
    (J beta : Real) (n : Nat) :
    multibondIsingPartition
        (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1)
          (c := 2 * n + 1))
        (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) =>
          beta * J) =
      2 * rectangularPrismPlusPartition J beta
        (2 * n + 1) (2 * n + 1) n := by
  rw [multibondIsingPartition_eq_two_mul_anchoredWeight none]
  unfold rectangularPrismPlusPartition Z
  congr 1
  rw [← Equiv.sum_comp (oddCubicalAnchoredEquivPrismConfig n)]
  apply Finset.sum_congr rfl
  intro s _
  unfold multibondIsingWeight
  congr 1
  rw [sum_oddCubicalDualAgreement_eq_plusPrismInteraction]
  unfold rectangularPrismPlusEnergy
  ring



theorem sum_oddCubicalCentralSheet_eq_prismInterface
    (J beta : Real) (n : Nat) (hn : 0 < n)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none) :
    (∑ p ∈ cubicalXYSheet
        (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)
        (⟨n + 1, by omega⟩ : Fin (2 * n + 2)),
        beta * J *
          (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2
            then (1 : Real) else -1)) =
      beta * J * rectangularPrismInterfaceInteraction
        (oddCubicalAnchoredEquivPrismConfig n s) := by
  classical
  unfold cubicalXYSheet
  rw [Finset.sum_image]
  · simp only [Fintype.sum_prod_type]
    rw [rectangularPrismInterfaceInteraction]
    simp only [hn, ↓reduceDIte]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    let z0 : Fin (2 * n) := ⟨n, by omega⟩
    have hp :
        (CubicalPlaquette.xy x y
          (⟨n + 1, by omega⟩ : Fin (2 * n + 2))) =
          oddPrismToCubicalPlaquette n (.zInternal x y z0) := by
      apply congrArg (CubicalPlaquette.xy x y)
      apply Fin.ext
      simp [z0]
    rw [hp, oddCubicalDualAgreement_eq_plusInteraction]
    simp [oddPrismPlusInteractionTerm, rectangularPrismSpin, z0]
  · intro a _ b _ hab
    simp at hab
    exact Prod.ext hab.1 hab.2



theorem sum_oddCubicalCentralTwist_eq_twistedPrismExponent
    (J beta : Real) (n : Nat) (hn : 0 < n)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none) :
    (∑ p : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1),
        multibondTwistCoupling
            (fun _ : CubicalPlaquette
              (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J)
            (cubicalXYSheet
              (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)
              (⟨n + 1, by omega⟩ : Fin (2 * n + 2))) p *
          (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2
            then (1 : Real) else -1)) =
      -beta * rectangularPrismTwistedEnergy J
        (oddCubicalAnchoredEquivPrismConfig n s) := by
  change (∑ p,
      reverseInteractionCoupling
          (fun _ : CubicalPlaquette
            (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J)
          (cubicalXYSheet
            (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)
            (⟨n + 1, by omega⟩ : Fin (2 * n + 2))) p *
        (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2
          then (1 : Real) else -1)) = _
  rw [sum_reverseInteractionCoupling,
    sum_oddCubicalDualAgreement_eq_plusPrismInteraction,
    sum_oddCubicalCentralSheet_eq_prismInterface J beta n hn]
  unfold rectangularPrismTwistedEnergy rectangularPrismPlusEnergy
  ring



theorem oddCubicalCentralTwistedPartition_eq_two_mul_twistedPrismPartition
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    multibondIsingPartition
        (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1)
          (c := 2 * n + 1))
        (multibondTwistCoupling
          (fun _ : CubicalPlaquette
            (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J)
          (cubicalXYSheet
            (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)
            (⟨n + 1, by omega⟩ : Fin (2 * n + 2)))) =
      2 * rectangularPrismTwistedPartition J beta
        (2 * n + 1) (2 * n + 1) n := by
  rw [multibondIsingPartition_eq_two_mul_anchoredWeight none]
  unfold rectangularPrismTwistedPartition Z
  congr 1
  rw [← Equiv.sum_comp (oddCubicalAnchoredEquivPrismConfig n)]
  apply Finset.sum_congr rfl
  intro s _
  unfold multibondIsingWeight
  congr 1
  exact sum_oddCubicalCentralTwist_eq_twistedPrismExponent J beta n hn s



theorem oddCubicalCentralDisorderFreeEnergy_eq_prism
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    multibondDisorderFreeEnergy
        (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1)
          (c := 2 * n + 1))
        (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) =>
          beta * J)
        (cubicalXYSheet
          (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)
          (⟨n + 1, by omega⟩ : Fin (2 * n + 2))) =
      StatMech.Ising.rectangularDobrushinFreeEnergy J beta
        (2 * n + 1) (2 * n + 1) n := by
  unfold multibondDisorderFreeEnergy
    StatMech.Ising.rectangularDobrushinFreeEnergy
  rw [oddCubicalDualPartition_eq_two_mul_plusPrismPartition,
    oddCubicalCentralTwistedPartition_eq_two_mul_twistedPrismPartition
      J beta n hn]
  have hp : rectangularPrismPlusPartition J beta
      (2 * n + 1) (2 * n + 1) n ≠ 0 := by
    unfold rectangularPrismPlusPartition
    exact (Z_pos beta _).ne'
  have ht : rectangularPrismTwistedPartition J beta
      (2 * n + 1) (2 * n + 1) n ≠ 0 := by
    unfold rectangularPrismTwistedPartition
    exact (Z_pos beta _).ne'
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hp,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) ht]
  ring



theorem centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity
    (beta : Real) (n : Nat) (hn : 0 < n) :
    centralCubicalIsingDisorderDensity beta n =
      rectangularPrismInterfaceDensity beta n := by
  unfold centralCubicalIsingDisorderDensity rectangularPrismInterfaceDensity
  dsimp
  congr 1
  simpa using
    oddCubicalCentralDisorderFreeEnergy_eq_prism 1 beta n hn



theorem standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity
    (beta : Real) (n : Nat) (hn : 0 < n) :
    standardCubicInterfaceDensity beta n =
      centralCubicalIsingDisorderDensity beta n := by
  rw [standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
      beta n hn,
    centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity
      beta n hn]



theorem hasPrismCubicalSurfaceComparison_iff_centralSheet
    (beta : Real) :
    HasPrismCubicalSurfaceComparison beta ↔
      Tendsto (fun n => centralCubicalIsingDisorderDensity beta n -
        oddCubicalIsingDisorderDensity beta n) atTop (nhds 0) := by
  constructor
  · intro h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity
      beta n (by omega)]
  · intro h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity
      beta n (by omega)]



theorem hasPrismCubicalSurfaceComparison_iff_standardSheet
    (beta : Real) :
    HasPrismCubicalSurfaceComparison beta ↔
      Tendsto (fun n => standardCubicInterfaceDensity beta n -
        oddCubicalIsingDisorderDensity beta n) atTop (nhds 0) := by
  rw [hasPrismCubicalSurfaceComparison_iff_centralSheet]
  constructor <;> intro h <;> apply h.congr' <;>
    filter_upwards [eventually_ge_atTop 1] with n hn <;>
    rw [standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity
      beta n (by omega)]



theorem standardCubicInterfaceDensity_tendsto_of_prismComparison
    {beta : Real} (hbeta : 0 < beta)
    (hprism : HasPrismCubicalSurfaceComparison beta) :
    Tendsto (standardCubicInterfaceDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension beta)) :=
  standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
    hbeta hprism (hasStandardPrismSurfaceComparison beta)



theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_prismComparison
    {betaC : Real}
    (hregime : StatMech.Ising.HasOrderedMagnetizationRegime
      (StatMech.Ising.magnetization 3) betaC)
    (hprism : forall beta, 0 < beta ->
      HasPrismCubicalSurfaceComparison beta)
    (hupper : forall n beta, 0 < beta ->
      standardCubicInterfaceDensity beta n <=
        2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
    (hweak : forall n,
      StatMech.Ising.HasWeakSurfaceTensionLowerBound 1
        (StatMech.Ising.magnetization 3)
        (fun beta => standardCubicInterfaceDensity beta n)) :
    forall beta, 0 < beta ->
      (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) :=
  rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds
    hregime hprism (fun beta _ => hasStandardPrismSurfaceComparison beta)
    hupper hweak

end

end StatMech.FrontierA
