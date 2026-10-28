/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSignCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYAllConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! Genuine original spin/Leech fibers for the proposed corrected Ninth source words.
No full-axis fixation or stabilizer cardinality is asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- The original local-fiber coercions need extra normalization during the generic basis proof.
/-- Every actual source low-code spin candidate is compatible with the genuine lattice sign. -/
theorem generatedNinth_lower_spin_sign_compatibility (k : Fin 11) :
    spinBinaryAction (monsterNortonYSpin (generatedNinthLowerSpinCode k)) =
      leechBinaryAction (monsterCo1GeometrySignIsometry (Fin.castAdd 1 k)) := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
  intro j
  have h := qBinaryAction_apply
    (spinConjugation (monsterNortonYSpin (generatedNinthLowerSpinCode k)))
      (xiSpinBinaryBasisLift j)
  change spinBinaryAction (monsterNortonYSpin (generatedNinthLowerSpinCode k))
    (Pi.single j 1) =
      toAdd (spinConjugation (monsterNortonYSpin (generatedNinthLowerSpinCode k))
        (xiSpinBinaryBasisLift j)).base at h
  rw [monsterNortonYSpin_conjugation,
    generatedNinth_lower_spin_sign_generator_certificate] at h
  have hm := monsterCo1GeometrySign_binary (Fin.castAdd 1 k) (Pi.single j 1)
  change leechBinaryAction (monsterCo1GeometrySignIsometry (Fin.castAdd 1 k))
    (Pi.single j 1) = _ at hm
  rw [Matrix.mulVec_single_one] at hm
  rw [Pi.basisFun_apply]
  simp only [LinearEquiv.coe_coe]
  exact h.trans hm.symm

/-- Each compatible low-code spin/Leech pair is an actual defining local fiber. -/
def generatedNinthLowerSpinSignFiber (k : Fin 11) : localFiberSubgroup :=
  ⟨(monsterNortonYSpin (generatedNinthLowerSpinCode k),
    monsterCo1GeometrySignIsometry (Fin.castAdd 1 k)),
    generatedNinth_lower_spin_sign_compatibility k⟩

/-- The complete genuine tensor operator retains the original source spin and physical sign. -/
theorem generatedNinth_lower_spin_sign_tensor (k : Fin 11)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedNinthLowerSpinSignFiber k) T t i =
      qSign (golayEncoder (monsterNortonYCode (generatedNinthLowerSpinCode k)) i) *
        (monsterNortonYSpin (generatedNinthLowerSpinCode k)).val (fun u => T u i) t := by
  rw [generatedFourth_local_tensor_columns]
  change (∑ j : Fin 24,
    (monsterCo1GeometrySignIsometry (Fin.castAdd 1 k)).val (Pi.single j 1) i *
      (monsterNortonYSpin (generatedNinthLowerSpinCode k)).val (fun u => T u j) t) = _
  have hc : monsterNortonYCode (generatedNinthLowerSpinCode k) =
      (Pi.single (Fin.castAdd 1 k) 1 : SpinIndex) :=
    generatedNinth_lower_spin_code_basis k
  rw [hc]
  simp only [monsterCo1GeometrySignIsometry, golaySignIsometry, golayRealSign_apply,
    monsterCo1GeometrySignCode, Pi.single_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The genuine sign fiber is exactly the original positive-triality source code word in G. -/
theorem generatedNinth_lower_spin_sign_generated (k : Fin 11) :
    localIntoGenerated (localFiberIntoH (generatedNinthLowerSpinSignFiber k)) =
      y555NortonActualY ⟨(generatedNinthLowerSpinCode k).val, by omega⟩ 0 := by
  obtain ⟨h, hh⟩ := monsterSourceY_word_mem_local
    (⟨(generatedNinthLowerSpinCode k).val, by omega⟩ : Fin 4096) 0
  have hρ : rhoLocal h = sExtra * rhoLocal
      (inclQ (sourceQCode ⟨(generatedNinthLowerSpinCode k).val, by omega⟩ 0)) * sExtra⁻¹ := by
    rw [y555NortonActualY_word] at hh
    exact congrArg Subtype.val hh
  have he : localFiberIntoH (generatedNinthLowerSpinSignFiber k) = h := by
    apply monsterLocalTensor_identifies
    intro x
    rw [generatedFourth_local_tensor, hρ]
    funext t i
    rw [generatedNinth_lower_spin_sign_tensor]
    exact (monsterNortonYAllWord_tensor (generatedNinthLowerSpinCode k) x t i).symm
  rw [he]
  exact hh

/-- Every primitive source letter has a concrete genuine local fiber. -/
def generatedNinthLowerSpinPositiveFiber (k : Fin 15) : localFiberSubgroup :=
  if h : k.val < 11 then generatedNinthLowerSpinSignFiber ⟨k.val, h⟩
  else if k.val = 11 then 1
  else if h' : k.val < 14 then monsterSourcePermutationFiber ⟨k.val - 12, by omega⟩
  else xiSpinLocalFiber

/-- Signed primitive letters use the actual group inverse. -/
def generatedNinthLowerSpinFiberLetter (l : GeneratedNinthLowerSpinLetter) :
    localFiberSubgroup :=
  if l.2 then (generatedNinthLowerSpinPositiveFiber l.1)⁻¹
  else generatedNinthLowerSpinPositiveFiber l.1

/-- The complete proposed source word is an element of the genuine local fiber product. -/
def generatedNinthLowerSpinSourceFiber (i : Fin 11) : localFiberSubgroup :=
  ((generatedNinthLowerSpinSourceWord i).map generatedNinthLowerSpinFiberLetter).prod

/-- The proposed full correction multiplies the actual source fiber on the left. -/
def generatedNinthLowerSpinCorrectedFiber (i : Fin 11) : localFiberSubgroup :=
  localFiberIncl (generatedNinthLowerSpinCorrection i) * generatedNinthLowerSpinSourceFiber i

/-- The proposed corrected generator belongs to the actual local group H. -/
def generatedNinthLowerSpinCorrectedLocal (i : Fin 11) : H :=
  localFiberIntoH (generatedNinthLowerSpinCorrectedFiber i)

/-- The original source fiber has its actual Conway projection, including all inverse letters. -/
theorem generatedNinth_lower_spin_source_projection (i : Fin 11) :
    projH (localFiberIntoH (generatedNinthLowerSpinSourceFiber i)) =
      (QuotientGroup.mk (generatedNinthLowerSpinSourceFiber i).val.2 : Co1) := rfl

/-- The actual Q correction preserves the entire original Conway projection. -/
theorem generatedNinth_lower_spin_corrected_projection (i : Fin 11) :
    projH (generatedNinthLowerSpinCorrectedLocal i) =
      (QuotientGroup.mk (generatedNinthLowerSpinSourceFiber i).val.2 : Co1) := by
  change projH (localFiberIntoH (localFiberIncl (generatedNinthLowerSpinCorrection i) *
    generatedNinthLowerSpinSourceFiber i)) = _
  rw [map_mul, map_mul]
  change projH (inclQ (generatedNinthLowerSpinCorrection i)) * _ = _
  rw [projH_inclQ, one_mul]
  rfl

/-- The proposed corrected generator is an actual element of the generated local image. -/
theorem generatedNinth_lower_spin_generated_membership (i : Fin 11) :
    localIntoGenerated (generatedNinthLowerSpinCorrectedLocal i) ∈
      localIntoGenerated.range :=
  ⟨generatedNinthLowerSpinCorrectedLocal i, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
