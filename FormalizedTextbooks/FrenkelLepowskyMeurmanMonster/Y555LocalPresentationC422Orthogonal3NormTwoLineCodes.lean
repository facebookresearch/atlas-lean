/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Independent canonical coordinates for all norm-two projective lines of the finite form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3FullGroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Canonical bounded codes whose decoded vectors have actual norm two. -/
def y422Orthogonal3NormTwoLinePredicate (c : Fin 6561) : Prop :=
  y422Orthogonal3VectorNorm (y422Orthogonal3VectorDecode c) = 2 ∧
    c.val ≤ y422Orthogonal3VectorCode (-y422Orthogonal3VectorDecode c)

/-- Actual independent norm and canonical sign checks are decidable finite computations. -/
instance y422Orthogonal3NormTwoLinePredicateDecidable (c : Fin 6561) :
    Decidable (y422Orthogonal3NormTwoLinePredicate c) := by
  unfold y422Orthogonal3NormTwoLinePredicate
  infer_instance

/-- All actual norm-two projective lines, represented by independent canonical field coordinates. -/
abbrev Y422Orthogonal3NormTwoLineCode :=
  {c : Fin 6561 // y422Orthogonal3NormTwoLinePredicate c}

/-- Negation preserves the exact independent quadratic value. -/
theorem y422Orthogonal3VectorNorm_neg (v : Fin 8 → ZMod 3) :
    y422Orthogonal3VectorNorm (-v) = y422Orthogonal3VectorNorm v := by
  simp [y422Orthogonal3VectorNorm, Matrix.mulVec_neg]

/-- The independent projective code of every actual vector has its exact finite coordinate bound. -/
theorem y422Orthogonal3ProjectiveVectorCode_lt (v : Fin 8 → ZMod 3) :
    y422Orthogonal3ProjectiveVectorCode v < 6561 :=
  (min_le_left _ _).trans_lt (y422Orthogonal3VectorCode_lt v)

/-- Canonical encoding sends every actual norm-two vector to its independent projective line. -/
def y422Orthogonal3NormTwoLineOfVector (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v = 2) : Y422Orthogonal3NormTwoLineCode :=
  ⟨⟨y422Orthogonal3ProjectiveVectorCode v, y422Orthogonal3ProjectiveVectorCode_lt v⟩, by
    unfold y422Orthogonal3NormTwoLinePredicate
    by_cases h : y422Orthogonal3VectorCode v ≤ y422Orthogonal3VectorCode (-v)
    · have he : (⟨y422Orthogonal3ProjectiveVectorCode v,
          y422Orthogonal3ProjectiveVectorCode_lt v⟩ : Fin 6561) =
        ⟨y422Orthogonal3VectorCode v, y422Orthogonal3VectorCode_lt v⟩ := by
        apply Fin.ext
        exact min_eq_left h
      rw [he, y422Orthogonal3VectorDecode_encode]
      exact ⟨hv, h⟩
    · have h' : y422Orthogonal3VectorCode (-v) ≤ y422Orthogonal3VectorCode v :=
        le_of_lt (lt_of_not_ge h)
      have he : (⟨y422Orthogonal3ProjectiveVectorCode v,
          y422Orthogonal3ProjectiveVectorCode_lt v⟩ : Fin 6561) =
        ⟨y422Orthogonal3VectorCode (-v), y422Orthogonal3VectorCode_lt (-v)⟩ := by
        apply Fin.ext
        exact min_eq_right h'
      rw [he, y422Orthogonal3VectorDecode_encode, neg_neg,
        y422Orthogonal3VectorNorm_neg]
      exact ⟨hv, h'⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- All 6561 independent field-coordinate labels are checked by exact quadratic arithmetic.
/-- The independently specified norm-two projective line set has exactly 1080 elements. -/
theorem y422Orthogonal3NormTwoLineCode_card :
    Fintype.card Y422Orthogonal3NormTwoLineCode = 1080 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
