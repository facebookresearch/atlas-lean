/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectIndexedPatternPushforward
import Code.FrontierD.FKRectHorizontalCylinderCrossings
import Code.FrontierD.FKRectRandomClusterEventFKG
import Code.FrontierD.FKRectTorusWindingCountBridge


















open Finset
open scoped BigOperators

namespace StatMech.FrontierD

open StatMech

noncomputable section


abbrev FKRectLocalPattern (R : FKRectTorus) (I : Finset R.EdgeIndex) :=
  ConfigSpace (↥I)


def fkRectLocalPatternExtension (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (eta : FKRectLocalPattern R I) :
    R.Configuration := fun a => if ha : a ∈ I then eta ⟨a, ha⟩ else false



def fkRectForceLocalPattern (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (eta : FKRectLocalPattern R I)
    (omega : R.Configuration) : R.Configuration :=
  fkRectForceIndexedPattern R I (fkRectLocalPatternExtension R I eta) omega

@[simp] theorem fkRectForceLocalPattern_of_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (eta : FKRectLocalPattern R I) (omega : R.Configuration)
    {a : R.EdgeIndex} (ha : a ∈ I) :
    fkRectForceLocalPattern R I eta omega a = eta ⟨a, ha⟩ := by
  simp [fkRectForceLocalPattern, fkRectLocalPatternExtension, ha]

@[simp] theorem fkRectForceLocalPattern_of_not_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (eta : FKRectLocalPattern R I) (omega : R.Configuration)
    {a : R.EdgeIndex} (ha : a ∉ I) :
    fkRectForceLocalPattern R I eta omega a = omega a := by
  simp [fkRectForceLocalPattern, ha]



theorem fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (eta : FKRectLocalPattern R I)
    (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceLocalPattern R I eta ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  exact
    fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
      R hq I (fkRectLocalPatternExtension R I eta) A




theorem fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (Source Target : Set R.Configuration)
    (hrepair : ∀ omega, omega ∈ Source →
      ∃ eta : FKRectLocalPattern R I,
        fkRectForceLocalPattern R I eta omega ∈ Target) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q Source ≤
      (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target := by
  classical
  let Pattern := FKRectLocalPattern R I
  let A : Pattern → Set R.Configuration := fun eta =>
    fkRectForceLocalPattern R I eta ⁻¹' Target
  have hsubset : Source ⊆
      fkRectFiniteEventUnion (Finset.univ : Finset Pattern) A := by
    intro omega homega
    obtain ⟨eta, heta⟩ := hrepair omega homega
    exact ⟨eta, Finset.mem_univ eta, heta⟩
  have hmono := fkRectCriticalEventMass_mono R
    (lt_of_lt_of_le zero_lt_one hq) hsubset
  have hunion := fkRectCriticalEventMass_finiteUnion_le_sum R
    (lt_of_lt_of_le zero_lt_one hq)
    (Finset.univ : Finset Pattern) A
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  calc
    FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalEventMass R q Source ≤
        FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalEventMass R q
            (fkRectFiniteEventUnion (Finset.univ : Finset Pattern) A) :=
      mul_le_mul_of_nonneg_left hmono (pow_nonneg hc _)
    _ ≤ FK.cFE (fkRectCriticalP q) q ^ I.card *
        ∑ eta : Pattern, fkRectCriticalEventMass R q (A eta) :=
      mul_le_mul_of_nonneg_left hunion (pow_nonneg hc _)
    _ = ∑ eta : Pattern,
        FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalEventMass R q (A eta) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _eta : Pattern, fkRectCriticalEventMass R q Target := by
      apply Finset.sum_le_sum
      intro eta heta
      exact
        fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event
          R hq I eta Target
    _ = (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target := by
      simp [Pattern, FKRectLocalPattern]


theorem fkRectCriticalWindingTailMass_eq_eventMass
    (R : FKRectTorus) (q : Real) (r : Nat) :
    fkRectCriticalWindingTailMass R q r =
      fkRectCriticalEventMass R q
        {omega | r ≤ fkRectUnorientedVerticalWindingNumber R omega} := by
  unfold fkRectCriticalWindingTailMass fkRectCriticalEventMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases htail : r ≤ fkRectUnorientedVerticalWindingNumber R omega <;>
    simp [Set.indicator, htail]




def FKRectWindingTailPrescribedCylinderRepair
    (R : FKRectTorus) (r : Nat) (I : Finset R.EdgeIndex)
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width)) : Prop :=
  ∀ omega, r ≤ fkRectUnorientedVerticalWindingNumber R omega →
    ∃ eta : FKRectLocalPattern R I,
      let tau := fkRectForceLocalPattern R I eta omega
      FKRectHorizontalCutClosedConfiguration R tau ∧
        FKRectHorizontalCylinderStablePairedWitnessCore R pair S tau




theorem fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (r : Nat)
    (I : Finset R.EdgeIndex) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width))
    (hrepair : FKRectWindingTailPrescribedCylinderRepair
      R r I pair S) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalWindingTailMass R q r ≤
      (2 ^ I.card : Nat) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} := by
  let A : Set R.Configuration :=
    {eta | FKRectHorizontalCylinderStablePairedWitnessCore R pair S eta}
  let Target : Set R.Configuration :=
    {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A}
  have htransfer :=
    fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair
      R hq I
      {omega | r ≤ fkRectUnorientedVerticalWindingNumber R omega}
      Target (by
        intro omega homega
        exact hrepair omega homega)
  rw [← fkRectCriticalWindingTailMass_eq_eventMass] at htransfer
  have hcutNonneg := fkRectCriticalHorizontalCutEventMass_nonneg
    R hq A
  have htarget : fkRectCriticalEventMass R q Target ≤
      fkRectCriticalHorizontalCutEventMass R q A := by
    have heq := closedMass_mul_fkRectCriticalHorizontalCutEventMass
      R hq A
    have hclosed := fkRectCriticalClosedMass_horizontalCut_le_one R hq
    change fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} ≤ _
    rw [← heq]
    exact mul_le_of_le_one_left hcutNonneg hclosed
  have hfactor : (0 : Real) ≤ (2 ^ I.card : Nat) := by positivity
  calc
    _ ≤ (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target :=
      htransfer
    _ ≤ (2 ^ I.card : Nat) *
        fkRectCriticalHorizontalCutEventMass R q A :=
      mul_le_mul_of_nonneg_left htarget hfactor
    _ = _ := by
      rw [fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass
        R pair hq S]



theorem fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (r perimeter : Nat)
    (I : Finset R.EdgeIndex) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width)) (hI : I.card ≤ perimeter)
    (hrepair : FKRectWindingTailPrescribedCylinderRepair
      R r I pair S) :
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
        fkRectCriticalWindingTailMass R q r ≤
      (2 ^ perimeter : Nat) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} := by
  let cylinderMass := StatMech.Probability.finiteEventMass
    (FK.fkProb (fkRectHorizontalCylinderGraph R)
      (fkRectCriticalP q) q)
    {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho}
  have hbase :=
    fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder
      R hq r I pair S hrepair
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  have hc1 : FK.cFE (fkRectCriticalP q) q ≤ 1 :=
    fkRectCritical_cFE_le_one hq
  have htail := fkRectCriticalWindingTailMass_nonneg
    R (lt_of_lt_of_le zero_lt_one hq) r
  have hcPow : FK.cFE (fkRectCriticalP q) q ^ perimeter ≤
      FK.cFE (fkRectCriticalP q) q ^ I.card :=
    pow_le_pow_of_le_one hc hc1 hI
  have htwoNat : 2 ^ I.card ≤ 2 ^ perimeter :=
    Nat.pow_le_pow_right (by omega) hI
  have htwo : ((2 ^ I.card : Nat) : Real) ≤
      ((2 ^ perimeter : Nat) : Real) := by
    exact_mod_cast htwoNat
  have hcylinder : 0 ≤ cylinderMass := by
    unfold cylinderMass StatMech.Probability.finiteEventMass
    apply Finset.sum_nonneg
    intro rho hrho
    split
    · exact FK.fkProb_nonneg
        (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
        (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
        (lt_of_lt_of_le zero_lt_one hq) rho
    · exact le_rfl
  calc
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
          fkRectCriticalWindingTailMass R q r ≤
        FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalWindingTailMass R q r :=
      mul_le_mul_of_nonneg_right hcPow htail
    _ ≤ (2 ^ I.card : Nat) * cylinderMass := hbase
    _ ≤ (2 ^ perimeter : Nat) * cylinderMass :=
      mul_le_mul_of_nonneg_right htwo hcylinder




def fkRectAfBottomIndex (R : FKRectTorus) (i : Nat) : Fin R.width :=
  ⟨(i + 1) % R.width, Nat.mod_lt _ R.width_pos⟩


def fkRectAfBottomIndexSet (R : FKRectTorus) (r : Nat) :
    Finset (Fin R.width) :=
  (Finset.range r).image (fkRectAfBottomIndex R)



theorem card_fkRectAfBottomIndexSet
    (R : FKRectTorus) (r : Nat) (hwidth : 2 * r ≤ R.width) :
    (fkRectAfBottomIndexSet R r).card = r := by
  unfold fkRectAfBottomIndexSet
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    have hi' : i < r := by simpa using hi
    have hj' : j < r := by simpa using hj
    have hiWidth : i + 1 < R.width := by
      omega
    have hjWidth : j + 1 < R.width := by
      omega
    have hval := congrArg Fin.val hij
    simp [fkRectAfBottomIndex, Nat.mod_eq_of_lt hiWidth,
      Nat.mod_eq_of_lt hjWidth] at hval
    omega



def fkRectAfPair (R : FKRectTorus) : Fin R.width → Fin R.width :=
  id



def FKRectAfWindingTailPrescribedCylinderRepair
    (R : FKRectTorus) (r : Nat) (I : Finset R.EdgeIndex) : Prop :=
  (fkRectAfBottomIndexSet R r).card = r ∧
    FKRectWindingTailPrescribedCylinderRepair R r I
      (fkRectAfPair R) (fkRectAfBottomIndexSet R r)

theorem fkRectAfWindingTailPrescribedCylinderRepair_of_sourceWidth
    (R : FKRectTorus) (r : Nat) (I : Finset R.EdgeIndex)
    (hwidth : 2 * r ≤ R.width)
    (hrepair : FKRectWindingTailPrescribedCylinderRepair R r I
      (fkRectAfPair R) (fkRectAfBottomIndexSet R r)) :
    FKRectAfWindingTailPrescribedCylinderRepair R r I := by
  exact ⟨card_fkRectAfBottomIndexSet R r hwidth, hrepair⟩


theorem fkRectCriticalWindingTailMass_cFE_perimeter_le_afCylinderEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (r perimeter : Nat)
    (I : Finset R.EdgeIndex) (hI : I.card ≤ perimeter)
    (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
        fkRectCriticalWindingTailMass R q r ≤
      (2 ^ perimeter : Nat) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness R
            (fkRectAfPair R) (fkRectAfBottomIndexSet R r) rho} := by
  exact
    fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder
      R hq r perimeter I (fkRectAfPair R)
      (fkRectAfBottomIndexSet R r) hI hrepair.2

end

end StatMech.FrontierD
