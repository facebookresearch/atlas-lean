/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizer

/-! Genuine corrected Golay stabilizer words fixing the standard coordinate octad pointwise. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Golay permutations fixing all eight standard-octad coordinates. -/
def generatedNinthStandardOctadPointwise : Subgroup golayAutomorphismSubgroup where
  carrier := {p | ∀ i : Fin 8, p.val (Fin.castAdd 16 i) = Fin.castAdd 16 i}
  one_mem' _ := rfl
  mul_mem' := by
    intro p q hp hq i
    change p.val (q.val (Fin.castAdd 16 i)) = _
    rw [hq i, hp i]
  inv_mem' := by
    intro p hp i
    change p.val.symm (Fin.castAdd 16 i) = _
    have h := congrArg p.val.symm (hp i)
    rw [p.val.symm_apply_apply] at h
    exact h.symm

/-- Original representative indices and their genuine correction words. -/
def generatedNinthStandardOctadRepresentativeIndices : Fin 16 → Fin 129 × Fin 129 :=
  ![(110, 126), (111, 128), (112, 127), (113, 127),
    (114, 126), (115, 128), (116, 127), (117, 127),
    (118, 128), (119, 128), (120, 127), (121, 127),
    (122, 128), (123, 128), (124, 127), (125, 127)]

/-- Actual Golay-preserving products of the original representative words. -/
def generatedNinthStandardOctadRepresentative (j : Fin 16) : golayAutomorphismSubgroup :=
  golayStabilizerAutomorphism (generatedNinthStandardOctadRepresentativeIndices j).1 *
    golayStabilizerAutomorphism (generatedNinthStandardOctadRepresentativeIndices j).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Bind all sixteen corrected words on the eight original octad coordinates.
/-- Every original corrected representative fixes the entire standard octad. -/
theorem generatedNinth_standard_octad_representative_fixed : ∀ j : Fin 16, ∀ i : Fin 8,
    (generatedNinthStandardOctadRepresentative j).val (Fin.castAdd 16 i) =
      Fin.castAdd 16 i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Bind each actual corrected word's image of the ninth physical coordinate.
/-- The sixteen actual corrected representatives have distinct outside images. -/
theorem generatedNinth_standard_octad_representative_outside : ∀ j : Fin 16,
    (generatedNinthStandardOctadRepresentative j).val 8 = Fin.natAdd 8 j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
