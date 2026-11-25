/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraph

/-! # Tests for exact covering system digraphs -/

open MetaMathlibExt

-- With shift 3, the rules 2m and -2m + 1 acquire offsets 3 and -10.
example (m n : ℤ) :
    ecsdAdj ![2, -2] ![3, -10] (-(m + 3)) (-(n + 3)) ↔ ecsdAdj ![2, -2] ![0, 1] m n := by
  obtain ⟨e, he⟩ := ecsdAdj_neg_shift_relIso ![2, -2] ![0, 1] 3
  have offsets : (fun i : Fin 2 => -(![(0 : ℤ), 1] i) + (![(2 : ℤ), -2] i - 1) * 3) =
      ![3, -10] := by
    exact funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  simpa only [he, offsets] using e.map_rel_iff (a := m) (b := n)

-- The empty family allows a length-zero walk at every vertex but has no loops.
example (d a : Fin 0 → ℤ) (m : ℤ) :
    IsKDescendant (ecsdAdj d a) 0 m m ∧ ¬IsDigraphCycle (ecsdAdj d a) [m] := by
  simp [isKDescendant_zero, isDigraphCycle_singleton, ecsdAdj]

-- The walk 3 → 0 → 2 uses the second offset on its first edge. The all-first-offset walk ends at 10.
example : (2 : ℤ) ≡ 10 [ZMOD 4] := by
  have h : IsKDescendant (ecsdAdj ![-2, -2] ![2, 6]) 2 3 2 := by
    refine ⟨0, (isKDescendant_one _ _ _).mpr ?_, ?_⟩
    · exact (ecsdAdj_two _ _ _ _ _ _).mpr (Or.inr rfl)
    · exact (ecsdAdj_two _ _ _ _ _ _).mpr (Or.inl rfl)
  exact ecsd_neg_two_descendant_modEq 2 6 3 2 2 h

-- Equal offsets give modulus zero, so the congruence determines the endpoint exactly.
example (m n : ℤ) (h : IsKDescendant (ecsdAdj ![-2, -2] ![2, 2]) 2 m n) :
    n = 4 * m - 2 := by
  have hn := ecsd_neg_two_descendant_modEq 2 2 m n 2 h
  change n ≡ 4 * m - 2 [ZMOD 0] at hn
  exact Int.modEq_zero_iff.mp hn
