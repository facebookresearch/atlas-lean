/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.MotzkinHumpLastUp

namespace MetaMathlibExt

-- At length three, the adjacent hump in UDF and the nonpeak in UFD have different end steps.
private def peak : MotzkinHumpFamily 3 := ⟨(1, ![2, 0, 1], 0, 1), by decide⟩
private def nonpeak : MotzkinHumpFamily 3 := ⟨(1, ![2, 1, 0], 0, 2), by decide⟩

example : ∃ e : MotzkinHumpFamily 3 ≃ MotzkinLastUpEvenFamily 3,
    EndsWithUp 3 (e peak).val.2 ∧ ¬ EndsWithUp 3 (e nonpeak).val.2 := by
  obtain ⟨e, _, h⟩ := motzkinHumpFamily_equiv_lastUpEvenFamily 3
  refine ⟨e, (h peak).mp ⟨peak.property.2.2.2, rfl⟩, fun hlast => ?_⟩
  have hnot : ¬ IsMotzkinPeak 3 1 ![2, 1, 0] 0 2 := by
    intro hpeak
    have := hpeak.2
    contradiction
  exact hnot ((h nonpeak).mpr hlast)

-- The proposed images UFU and UUF both end at height two, but only UFU ends in U.
-- These checks use the concrete words, independently of the equivalence theorem.
example : IsMotzkinPrefix 3 2 ![2, 1, 2] ∧ IsMotzkinPrefix 3 2 ![2, 2, 1] ∧
    EndsWithUp 3 ![2, 1, 2] ∧ ¬ EndsWithUp 3 ![2, 2, 1] := by
  simp only [endsWithUp_iff]
  decide

example : IsMotzkinPeak 3 1 ![2, 0, 1] 0 1 ∧ ¬ IsMotzkinPeak 3 1 ![2, 1, 0] 0 2 := by
  simp only [isMotzkinPeak_iff]
  decide

example : IsMotzkinHump 4 2 ![2, 2, 0, 0] 1 2 ∧ IsMotzkinPrefix 4 4 ![2, 2, 2, 2] := by
  decide

-- The peak of height two in UUDD retains its label, so its image is at height four.
example : ∃ e : MotzkinHumpFamily 4 ≃ MotzkinLastUpEvenFamily 4,
    ∃ q : MotzkinHumpFamily 4, q.val = (2, ![2, 2, 0, 0], 1, 2) ∧
      (e q).val.1 = 2 ∧ IsMotzkinPrefix 4 4 (e q).val.2 := by
  obtain ⟨e, h, _⟩ := motzkinHumpFamily_equiv_lastUpEvenFamily 4
  let q : MotzkinHumpFamily 4 := ⟨(2, ![2, 2, 0, 0], 1, 2), by decide⟩
  have hk : (e q).val.1 = 2 := h q
  refine ⟨e, q, rfl, hk, ?_⟩
  have hp := (e q).property.2.2.1
  rw [hk] at hp
  exact hp

end MetaMathlibExt
