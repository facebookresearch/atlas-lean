/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Walls.jc_earanchor
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice










noncomputable def jc_shiftX (c : Site 2) (j : ℤ) : Site 2 := c + ![j, 0]


theorem jc_shiftX_coord0 (c : Site 2) (j : ℤ) : (jc_shiftX c j) 0 = c 0 + j := by
  simp [jc_shiftX, Pi.add_apply]


theorem jc_shiftX_coord1 (c : Site 2) (j : ℤ) : (jc_shiftX c j) 1 = c 1 := by
  simp [jc_shiftX, Pi.add_apply]


theorem jc_shiftX_zero (c : Site 2) : jc_shiftX c 0 = c := by
  funext i; fin_cases i <;> simp [jc_shiftX, Pi.add_apply]











def jc_RunLengths (K : Set (Site 2)) (c : Site 2) : Set ℕ :=
  {n | ∀ j : ℕ, j ≤ n → jc_shiftX c (j : ℤ) ∈ K}



theorem jc_zero_mem_runLengths (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K) :
    0 ∈ jc_RunLengths K c := by
  intro j hj
  interval_cases j
  rw [Nat.cast_zero, jc_shiftX_zero]
  exact hc




theorem jc_runLengths_bddAbove (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) :
    BddAbove (jc_RunLengths K c) := by
  classical
  have himg : (((fun v => v 0) '' K)).Finite := hK.image _
  obtain ⟨M, hM⟩ := himg.bddAbove
  refine ⟨(M - c 0).toNat, ?_⟩
  intro n hn
  have hmem : jc_shiftX c (n : ℤ) ∈ K := hn n (le_refl n)
  have hle : (jc_shiftX c (n : ℤ)) 0 ≤ M := hM ⟨_, hmem, rfl⟩
  rw [jc_shiftX_coord0] at hle
  omega



noncomputable def jc_runMax (K : Set (Site 2)) (c : Site 2) : ℕ := sSup (jc_RunLengths K c)




theorem jc_runMax_mem (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : c ∈ K) :
    jc_runMax K c ∈ jc_RunLengths K c := by
  apply Nat.sSup_mem
  · exact ⟨0, jc_zero_mem_runLengths K c hc⟩
  · exact jc_runLengths_bddAbove K hK c



theorem jc_runMax_succ_not_mem (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) :
    jc_runMax K c + 1 ∉ jc_RunLengths K c := by
  intro hmem
  have hle : jc_runMax K c + 1 ≤ jc_runMax K c :=
    le_csSup (jc_runLengths_bddAbove K hK c) hmem
  omega





theorem jc_runMax_succ_nmem_K (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : c ∈ K) :
    jc_shiftX c ((jc_runMax K c : ℤ) + 1) ∉ K := by
  intro hmem
  apply jc_runMax_succ_not_mem K hK c
  intro j hj
  rcases Nat.lt_or_ge j (jc_runMax K c + 1) with h | h
  · exact jc_runMax_mem K hK c hc j (by omega)
  · have hj' : j = jc_runMax K c + 1 := by omega
    subst hj'
    push_cast
    exact hmem




















structure jc_TopRowRun (K : Set (Site 2)) (c : Site 2) (L : ℕ) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  run_mem : ∀ j : ℕ, j ≤ L → jc_shiftX c (j : ℤ) ∈ K
  
  run_maximal : jc_shiftX c ((L : ℤ) + 1) ∉ K
  
  run_topRow : ∀ j : ℕ, (jc_shiftX c (j : ℤ)) 1 = c 1
  
  topRow_maximal : ∀ v ∈ K, v 1 ≤ c 1
  
  leftMost : jc_shiftX c (-1) ∉ K






theorem jc_extremeCell_topRowRun (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : jc_TopRowRun K c (jc_runMax K c) where
  isExtreme := hc
  run_mem := jc_runMax_mem K hK c hc.mem
  run_maximal := jc_runMax_succ_nmem_K K hK c hc.mem
  run_topRow := fun j => jc_shiftX_coord1 c (j : ℤ)
  topRow_maximal := fun v hv => by
    by_contra h
    rw [not_le] at h
    exact extremeCell_not_mem_of_higher K c v hc h hv
  leftMost := by
    have hnmem := extremeCell_head_nmem K c hc
    rw [leftDart_head] at hnmem
    have hshift : jc_shiftX c (-1) = c + ![-1, 0] := by rw [jc_shiftX]
    rw [hshift]
    exact hnmem










theorem jc_topRowRun_of_earAnchor (K : Set (Site 2)) (hK : K.Finite) {c : Site 2}
    (hanchor : jc_EarAnchor K c) : jc_TopRowRun K c (jc_runMax K c) :=
  jc_extremeCell_topRowRun K hK c hanchor.isExtreme







theorem jc_topRowRun (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c L, jc_TopRowRun K c L := by
  obtain ⟨c, hanchor⟩ := jc_earAnchor K hK hne
  exact ⟨c, jc_runMax K c, jc_topRowRun_of_earAnchor K hK hanchor⟩






theorem jc_topRowRun_explicit (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c L, c ∈ K ∧ (∀ j : ℕ, j ≤ L → jc_shiftX c (j : ℤ) ∈ K) ∧
      jc_shiftX c ((L : ℤ) + 1) ∉ K ∧ (∀ j : ℕ, (jc_shiftX c (j : ℤ)) 1 = c 1) ∧
      (∀ v ∈ K, v 1 ≤ c 1) ∧ jc_shiftX c (-1) ∉ K := by
  obtain ⟨c, L, hrun⟩ := jc_topRowRun K hK hne
  exact ⟨c, L, hrun.isExtreme.mem, hrun.run_mem, hrun.run_maximal, hrun.run_topRow,
    hrun.topRow_maximal, hrun.leftMost⟩









theorem jc_unitCell_topRowRun : ∃ c L, jc_TopRowRun unitCell c L :=
  jc_topRowRun unitCell unitCell_finite ⟨_, origin_mem_unitCell⟩

end Walls

end StatMech
