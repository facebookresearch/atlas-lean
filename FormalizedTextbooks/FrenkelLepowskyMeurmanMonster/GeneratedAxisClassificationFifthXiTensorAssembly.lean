/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorCertificate7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorFixed

/-! All original support certificates establish the genuine full corrected Xi tensor action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All 128 actual signed support coordinates pass the genuine corrected Xi numerator check. -/
theorem generatedFifth_xi_tensor_certificate (j : Fin 64) (h : ZMod 2) :
    generatedFifthXiCorrectedTensorNumerator (generatedFifthXiTensorAddress j h)
      (generatedFifthOddRootOutputData j).2 = 16 * generatedFifthXiTensorWeight j h := by
  let k : Fin 8 := ⟨j.val % 8, by omega⟩
  generalize hb : j.val / 8 = b
  have hblt : b < 8 := by omega
  have hm : j.val = 8 * b + k.val := by dsimp [k]; omega
  interval_cases b
  · have hj : j = ⟨0 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate0 k h
  · have hj : j = ⟨8 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate1 k h
  · have hj : j = ⟨16 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate2 k h
  · have hj : j = ⟨24 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate3 k h
  · have hj : j = ⟨32 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate4 k h
  · have hj : j = ⟨40 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate5 k h
  · have hj : j = ⟨48 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate6 k h
  · have hj : j = ⟨56 + k.val, by omega⟩ := by
      apply Fin.ext
      simpa using hm
    rw [hj]
    exact generatedFifth_xi_tensor_certificate7 k h

/-- The actual Q-corrected Xi fiber fixes the entire original fifth tensor block. -/
theorem generatedFifth_xi_tensor_fixed :
    localTensorRepresentation generatedFifthXiCorrectedFiber
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 :=
  generatedFifth_xi_tensor_fixed_of_certificate generatedFifth_xi_tensor_certificate

/-- The literal local fiber action fixes the original encoded tensor coordinate. -/
theorem generatedFifth_xi_encoded_tensor_fixed :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthXiCorrectedFiber)
      generatedFifthAxis)).2.2 = (griessConwayEncode generatedFifthAxis).2.2 := by
  rw [generatedFourth_local_tensor]
  exact generatedFifth_xi_tensor_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
