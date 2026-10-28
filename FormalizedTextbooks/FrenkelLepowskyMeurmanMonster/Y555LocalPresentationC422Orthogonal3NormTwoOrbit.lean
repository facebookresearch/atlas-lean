/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked original source-path actions cover every independent norm-two projective line. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3SortedPathCodes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3FullPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3FixedReflection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ProjectiveCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Every actual inverse source-path image of the fixed vector has its original norm two. -/
theorem y422Orthogonal3TPathVector_norm_two (i : Fin 9033) :
    y422Orthogonal3VectorNorm (y422Orthogonal3TPathVector i) = 2 := by
  unfold y422Orthogonal3TPathVector
  rw [y422Orthogonal3FullGroup_norm _
    (y422Orthogonal3FullGroup.inv_mem (y422Orthogonal3TPathValue_mem_full i))]
  exact y422Orthogonal3FixedVector_norm_two

/-- Each of the 1080 actual original orbit paths defines an independent norm-two projective line. -/
noncomputable def y422Orthogonal3NormTwoOrbitLine (i : Fin 1080) :
    Y422Orthogonal3NormTwoLineCode :=
  y422Orthogonal3NormTwoLineOfVector
    (y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i))
    (y422Orthogonal3TPathVector_norm_two (y422Orthogonal3SortedPath i))

/-- The actual source-orbit line retains its exact checked canonical code. -/
theorem y422Orthogonal3NormTwoOrbitLine_value (i : Fin 1080) :
    (y422Orthogonal3NormTwoOrbitLine i).val.val = y422Orthogonal3SortedCode i :=
  y422Orthogonal3SortedCode_actual i

/-- Actual original source paths give distinct independent norm-two projective lines. -/
theorem y422Orthogonal3NormTwoOrbitLine_injective :
    Function.Injective y422Orthogonal3NormTwoOrbitLine := by
  intro i j h
  apply y422Orthogonal3SortedCode_strictMono.injective
  have hc := congrArg (fun c : Y422Orthogonal3NormTwoLineCode => c.val.val) h
  simpa only [y422Orthogonal3NormTwoOrbitLine_value] using hc

/-- The checked 1080 source paths cover the entire independently counted projective line set. -/
theorem y422Orthogonal3NormTwoOrbitLine_surjective :
    Function.Surjective y422Orthogonal3NormTwoOrbitLine := by
  have hc : Nat.card Y422Orthogonal3NormTwoLineCode ≤ Nat.card (Fin 1080) := by
    rw [Nat.card_eq_fintype_card, y422Orthogonal3NormTwoLineCode_card, Nat.card_fin]
  exact (y422Orthogonal3NormTwoOrbitLine_injective.bijective_of_nat_card_le hc).2

/-- Every independent norm-two vector is an actual original source-path image up to sign. -/
theorem y422Orthogonal3NormTwo_source_cover (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v = 2) :
    ∃ i : Fin 1080,
      v = y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i) ∨
      v = -y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i) := by
  obtain ⟨i, hi⟩ := y422Orthogonal3NormTwoOrbitLine_surjective
    (y422Orthogonal3NormTwoLineOfVector v hv)
  have hc := congrArg (fun c : Y422Orthogonal3NormTwoLineCode => c.val.val) hi
  change y422Orthogonal3ProjectiveVectorCode
      (y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i)) =
    y422Orthogonal3ProjectiveVectorCode v at hc
  exact ⟨i, (y422Orthogonal3ProjectiveVectorCode_eq_iff v _).mp hc.symm⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
