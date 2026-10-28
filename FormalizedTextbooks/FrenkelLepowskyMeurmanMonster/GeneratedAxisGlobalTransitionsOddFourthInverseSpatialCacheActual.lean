/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck00_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck00_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck00_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck00_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck01_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck01_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck01_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck01_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck02_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck02_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck02_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck02_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck03_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck03_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck03_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheCheck03_03

/-! The entire original physical inverse action is bound at every coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All original inverse physical coefficients are exactly the checked signed half-integers. -/
theorem generatedAxisGlobalOddFourthInverseSpatialNumerator_actual (k : Fin 4) (i j : Fin 24) :
    generatedAxisGlobalRationalSpatialInverseMatrix (generatedAxisGlobalOddFourthComparisonLetters k) i j =
      (generatedAxisGlobalOddFourthInverseSpatialNumerator k i j : ℚ) / 2 := by
  fin_cases k
  · by_cases h0 : j.val < 6
    · let q : Fin 6 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck00_00 i q
      rw [hj] at h
      exact h
    by_cases h1 : j.val < 12
    · let q : Fin 6 := ⟨j.val-6, by omega⟩
      have hj : (⟨6+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck00_01 i q
      rw [hj] at h
      exact h
    by_cases h2 : j.val < 18
    · let q : Fin 6 := ⟨j.val-12, by omega⟩
      have hj : (⟨12+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck00_02 i q
      rw [hj] at h
      exact h
    let q : Fin 6 := ⟨j.val-18, by omega⟩
    have hj : (⟨18+q.val, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp only [q]
      omega
    have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck00_03 i q
    rw [hj] at h
    exact h
  · by_cases h0 : j.val < 6
    · let q : Fin 6 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck01_00 i q
      rw [hj] at h
      exact h
    by_cases h1 : j.val < 12
    · let q : Fin 6 := ⟨j.val-6, by omega⟩
      have hj : (⟨6+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck01_01 i q
      rw [hj] at h
      exact h
    by_cases h2 : j.val < 18
    · let q : Fin 6 := ⟨j.val-12, by omega⟩
      have hj : (⟨12+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck01_02 i q
      rw [hj] at h
      exact h
    let q : Fin 6 := ⟨j.val-18, by omega⟩
    have hj : (⟨18+q.val, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp only [q]
      omega
    have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck01_03 i q
    rw [hj] at h
    exact h
  · by_cases h0 : j.val < 6
    · let q : Fin 6 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck02_00 i q
      rw [hj] at h
      exact h
    by_cases h1 : j.val < 12
    · let q : Fin 6 := ⟨j.val-6, by omega⟩
      have hj : (⟨6+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck02_01 i q
      rw [hj] at h
      exact h
    by_cases h2 : j.val < 18
    · let q : Fin 6 := ⟨j.val-12, by omega⟩
      have hj : (⟨12+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck02_02 i q
      rw [hj] at h
      exact h
    let q : Fin 6 := ⟨j.val-18, by omega⟩
    have hj : (⟨18+q.val, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp only [q]
      omega
    have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck02_03 i q
    rw [hj] at h
    exact h
  · by_cases h0 : j.val < 6
    · let q : Fin 6 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck03_00 i q
      rw [hj] at h
      exact h
    by_cases h1 : j.val < 12
    · let q : Fin 6 := ⟨j.val-6, by omega⟩
      have hj : (⟨6+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck03_01 i q
      rw [hj] at h
      exact h
    by_cases h2 : j.val < 18
    · let q : Fin 6 := ⟨j.val-12, by omega⟩
      have hj : (⟨12+q.val, by omega⟩ : Fin 24) = j := by
        apply Fin.ext
        dsimp only [q]
        omega
      have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck03_02 i q
      rw [hj] at h
      exact h
    let q : Fin 6 := ⟨j.val-18, by omega⟩
    have hj : (⟨18+q.val, by omega⟩ : Fin 24) = j := by
      apply Fin.ext
      dsimp only [q]
      omega
    have h := generatedAxisGlobalOddFourthInverseSpatialCacheCheck03_03 i q
    rw [hj] at h
    exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
