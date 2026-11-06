/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabels

/-! Explicit candidate bases for intrinsic fifteen-frame systems. Enumeration data
is checked against the actual intrinsic form before it is used as a system. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Little-endian binary coordinates of an eight-bit label. -/
def generatedAxisE8FrameBits (x : Fin 256) : Fin 8 → ZMod 2 :=
  generatedAxisE8FrameLabelBits x

set_option maxRecDepth 10000 in
-- The explicit270-row literal has a deeply nested tuple representation.
/-- Four displayed independent eight-bit root-coordinate labels for each candidate. -/
def generatedAxisE8FrameSystemBasisLabels : Fin 270 → Fin 4 → Fin 256 :=
  ![
    ![7, 25, 42, 65],
    ![7, 25, 42, 193],
    ![7, 25, 43, 65],
    ![7, 25, 43, 193],
    ![7, 25, 106, 129],
    ![7, 25, 107, 129],
    ![7, 26, 41, 65],
    ![7, 26, 41, 193],
    ![7, 26, 43, 65],
    ![7, 26, 43, 193],
    ![7, 26, 104, 130],
    ![7, 26, 106, 130],
    ![7, 27, 41, 65],
    ![7, 27, 41, 193],
    ![7, 27, 42, 65],
    ![7, 27, 42, 193],
    ![7, 27, 104, 131],
    ![7, 27, 107, 131],
    ![7, 41, 90, 129],
    ![7, 41, 91, 129],
    ![7, 42, 88, 130],
    ![7, 42, 90, 130],
    ![7, 43, 88, 131],
    ![7, 43, 91, 131],
    ![7, 49, 90, 129],
    ![7, 49, 91, 129],
    ![7, 50, 88, 130],
    ![7, 50, 90, 130],
    ![7, 51, 88, 131],
    ![7, 51, 91, 131],
    ![11, 21, 38, 65],
    ![11, 21, 38, 193],
    ![11, 21, 39, 65],
    ![11, 21, 39, 193],
    ![11, 21, 102, 129],
    ![11, 21, 103, 129],
    ![11, 22, 37, 65],
    ![11, 22, 37, 193],
    ![11, 22, 39, 65],
    ![11, 22, 39, 193],
    ![11, 22, 100, 130],
    ![11, 22, 102, 130],
    ![11, 23, 37, 65],
    ![11, 23, 37, 193],
    ![11, 23, 38, 65],
    ![11, 23, 38, 193],
    ![11, 23, 100, 131],
    ![11, 23, 103, 131],
    ![11, 37, 86, 129],
    ![11, 37, 87, 129],
    ![11, 38, 84, 130],
    ![11, 38, 86, 130],
    ![11, 39, 84, 131],
    ![11, 39, 87, 131],
    ![11, 49, 86, 129],
    ![11, 49, 87, 129],
    ![11, 50, 84, 130],
    ![11, 50, 86, 130],
    ![11, 51, 84, 131],
    ![11, 51, 87, 131],
    ![13, 19, 38, 65],
    ![13, 19, 38, 193],
    ![13, 19, 39, 65],
    ![13, 19, 39, 193],
    ![13, 19, 102, 129],
    ![13, 19, 103, 129],
    ![13, 22, 35, 65],
    ![13, 22, 35, 193],
    ![13, 22, 39, 65],
    ![13, 22, 39, 193],
    ![13, 22, 98, 132],
    ![13, 22, 102, 132],
    ![13, 23, 35, 65],
    ![13, 23, 35, 193],
    ![13, 23, 38, 65],
    ![13, 23, 38, 193],
    ![13, 23, 98, 133],
    ![13, 23, 103, 133],
    ![13, 35, 86, 129],
    ![13, 35, 87, 129],
    ![13, 38, 82, 132],
    ![13, 38, 86, 132],
    ![13, 39, 82, 133],
    ![13, 39, 87, 133],
    ![13, 49, 86, 129],
    ![13, 49, 87, 129],
    ![13, 52, 82, 132],
    ![13, 52, 86, 132],
    ![13, 53, 82, 133],
    ![13, 53, 87, 133],
    ![14, 19, 37, 65],
    ![14, 19, 37, 193],
    ![14, 19, 39, 65],
    ![14, 19, 39, 193],
    ![14, 19, 100, 130],
    ![14, 19, 102, 130],
    ![14, 21, 35, 65],
    ![14, 21, 35, 193],
    ![14, 21, 39, 65],
    ![14, 21, 39, 193],
    ![14, 21, 98, 132],
    ![14, 21, 102, 132],
    ![14, 23, 35, 65],
    ![14, 23, 35, 193],
    ![14, 23, 37, 65],
    ![14, 23, 37, 193],
    ![14, 23, 98, 134],
    ![14, 23, 100, 134],
    ![14, 35, 84, 130],
    ![14, 35, 86, 130],
    ![14, 37, 82, 132],
    ![14, 37, 86, 132],
    ![14, 39, 82, 134],
    ![14, 39, 84, 134],
    ![14, 50, 84, 130],
    ![14, 50, 86, 130],
    ![14, 52, 82, 132],
    ![14, 52, 86, 132],
    ![14, 54, 82, 134],
    ![14, 54, 84, 134],
    ![15, 19, 37, 65],
    ![15, 19, 37, 193],
    ![15, 19, 38, 65],
    ![15, 19, 38, 193],
    ![15, 19, 100, 131],
    ![15, 19, 103, 131],
    ![15, 21, 35, 65],
    ![15, 21, 35, 193],
    ![15, 21, 38, 65],
    ![15, 21, 38, 193],
    ![15, 21, 98, 133],
    ![15, 21, 103, 133],
    ![15, 22, 35, 65],
    ![15, 22, 35, 193],
    ![15, 22, 37, 65],
    ![15, 22, 37, 193],
    ![15, 22, 98, 134],
    ![15, 22, 100, 134],
    ![15, 35, 84, 131],
    ![15, 35, 87, 131],
    ![15, 37, 82, 133],
    ![15, 37, 87, 133],
    ![15, 38, 82, 134],
    ![15, 38, 84, 134],
    ![15, 51, 84, 131],
    ![15, 51, 87, 131],
    ![15, 53, 82, 133],
    ![15, 53, 87, 133],
    ![15, 54, 82, 134],
    ![15, 54, 84, 134],
    ![19, 37, 78, 129],
    ![19, 37, 79, 129],
    ![19, 38, 76, 130],
    ![19, 38, 78, 130],
    ![19, 39, 76, 131],
    ![19, 39, 79, 131],
    ![19, 41, 78, 129],
    ![19, 41, 79, 129],
    ![19, 42, 76, 130],
    ![19, 42, 78, 130],
    ![19, 43, 76, 131],
    ![19, 43, 79, 131],
    ![21, 35, 78, 129],
    ![21, 35, 79, 129],
    ![21, 38, 74, 132],
    ![21, 38, 78, 132],
    ![21, 39, 74, 133],
    ![21, 39, 79, 133],
    ![21, 41, 78, 129],
    ![21, 41, 79, 129],
    ![21, 44, 74, 132],
    ![21, 44, 78, 132],
    ![21, 45, 74, 133],
    ![21, 45, 79, 133],
    ![22, 35, 76, 130],
    ![22, 35, 78, 130],
    ![22, 37, 74, 132],
    ![22, 37, 78, 132],
    ![22, 39, 74, 134],
    ![22, 39, 76, 134],
    ![22, 42, 76, 130],
    ![22, 42, 78, 130],
    ![22, 44, 74, 132],
    ![22, 44, 78, 132],
    ![22, 46, 74, 134],
    ![22, 46, 76, 134],
    ![23, 35, 76, 131],
    ![23, 35, 79, 131],
    ![23, 37, 74, 133],
    ![23, 37, 79, 133],
    ![23, 38, 74, 134],
    ![23, 38, 76, 134],
    ![23, 43, 76, 131],
    ![23, 43, 79, 131],
    ![23, 45, 74, 133],
    ![23, 45, 79, 133],
    ![23, 46, 74, 134],
    ![23, 46, 76, 134],
    ![25, 35, 78, 129],
    ![25, 35, 79, 129],
    ![25, 37, 78, 129],
    ![25, 37, 79, 129],
    ![25, 42, 70, 136],
    ![25, 42, 78, 136],
    ![25, 43, 70, 137],
    ![25, 43, 79, 137],
    ![25, 44, 70, 136],
    ![25, 44, 78, 136],
    ![25, 45, 70, 137],
    ![25, 45, 79, 137],
    ![26, 35, 76, 130],
    ![26, 35, 78, 130],
    ![26, 38, 76, 130],
    ![26, 38, 78, 130],
    ![26, 41, 70, 136],
    ![26, 41, 78, 136],
    ![26, 43, 70, 138],
    ![26, 43, 76, 138],
    ![26, 44, 70, 136],
    ![26, 44, 78, 136],
    ![26, 46, 70, 138],
    ![26, 46, 76, 138],
    ![27, 35, 76, 131],
    ![27, 35, 79, 131],
    ![27, 39, 76, 131],
    ![27, 39, 79, 131],
    ![27, 41, 70, 137],
    ![27, 41, 79, 137],
    ![27, 42, 70, 138],
    ![27, 42, 76, 138],
    ![27, 45, 70, 137],
    ![27, 45, 79, 137],
    ![27, 46, 70, 138],
    ![27, 46, 76, 138],
    ![28, 37, 74, 132],
    ![28, 37, 78, 132],
    ![28, 38, 74, 132],
    ![28, 38, 78, 132],
    ![28, 41, 70, 136],
    ![28, 41, 78, 136],
    ![28, 42, 70, 136],
    ![28, 42, 78, 136],
    ![28, 45, 70, 140],
    ![28, 45, 74, 140],
    ![28, 46, 70, 140],
    ![28, 46, 74, 140],
    ![29, 37, 74, 133],
    ![29, 37, 79, 133],
    ![29, 39, 74, 133],
    ![29, 39, 79, 133],
    ![29, 41, 70, 137],
    ![29, 41, 79, 137],
    ![29, 43, 70, 137],
    ![29, 43, 79, 137],
    ![29, 44, 70, 140],
    ![29, 44, 74, 140],
    ![29, 46, 70, 140],
    ![29, 46, 74, 140],
    ![30, 38, 74, 134],
    ![30, 38, 76, 134],
    ![30, 39, 74, 134],
    ![30, 39, 76, 134],
    ![30, 42, 70, 138],
    ![30, 42, 76, 138],
    ![30, 43, 70, 138],
    ![30, 43, 76, 138],
    ![30, 44, 70, 140],
    ![30, 44, 74, 140],
    ![30, 45, 70, 140],
    ![30, 45, 74, 140]]

/-- Four actual intrinsic root-coordinate vectors of each displayed candidate. -/
def generatedAxisE8FrameSystemCandidateBasis (k : Fin 270) (j : Fin 4) : Fin 8 → ZMod 2 :=
  generatedAxisE8FrameBits (generatedAxisE8FrameSystemBasisLabels k j)

/-- The four-column intrinsic linear map of a displayed candidate. -/
def generatedAxisE8FrameSystemCandidateMap (k : Fin 270) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  Matrix.mulVecLin (fun i j => generatedAxisE8FrameSystemCandidateBasis k j i)

/-- The eight-bit xor of the selected basis labels for a coefficient vector. -/
def generatedAxisE8FrameSystemCandidateLabel (k : Fin 270) (a : Fin 4 → ZMod 2) : Fin 256 :=
  generatedAxisE8FrameLabelXor
    (generatedAxisE8FrameLabelXor
      (if a 0 = 0 then 0 else generatedAxisE8FrameSystemBasisLabels k 0)
      (if a 1 = 0 then 0 else generatedAxisE8FrameSystemBasisLabels k 1))
    (generatedAxisE8FrameLabelXor
      (if a 2 = 0 then 0 else generatedAxisE8FrameSystemBasisLabels k 2)
      (if a 3 = 0 then 0 else generatedAxisE8FrameSystemBasisLabels k 3))

/-- Matrix multiplication agrees with the compact xor label, for every coefficient vector. -/
theorem generatedAxisE8FrameSystemCandidateMap_bits (k : Fin 270) (a : Fin 4 → ZMod 2) :
    generatedAxisE8FrameSystemCandidateMap k a =
      generatedAxisE8FrameLabelBits (generatedAxisE8FrameSystemCandidateLabel k a) := by
  have hb : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide +kernel
  have hz : generatedAxisE8FrameLabelBits 0 = 0 := by
    ext i; simp [generatedAxisE8FrameLabelBits]
  have hm : generatedAxisE8FrameSystemCandidateMap k a =
      ∑ j, a j • generatedAxisE8FrameLabelBits (generatedAxisE8FrameSystemBasisLabels k j) := by
    ext i
    change (∑ j, generatedAxisE8FrameLabelBits
      (generatedAxisE8FrameSystemBasisLabels k j) i * a j) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hm]
  rcases hb (a 0) with h0 | h0 <;> rcases hb (a 1) with h1 | h1 <;>
    rcases hb (a 2) with h2 | h2 <;> rcases hb (a 3) with h3 | h3 <;>
    simp [Fin.sum_univ_succ, generatedAxisE8FrameSystemCandidateLabel,
      generatedAxisE8FrameLabelBits_xor, hz, h0, h1, h2, h3, add_assoc]

set_option maxHeartbeats 200000000 in
-- All270 candidates have only16 compact coefficient labels each.
set_option maxRecDepth 10000 in
-- Finite coefficient function enumeration requires deeper reduction.
/-- The compact basis-label maps have trivial kernel. -/
theorem generatedAxisE8FrameSystemCandidateLabel_zero_certificate :
    ∀ (k : Fin 270) (a : Fin 4 → ZMod 2),
      generatedAxisE8FrameSystemCandidateLabel k a = 0 → a = 0 := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Only4320 compact eight-bit labels are checked against the verified singular mask.
set_option maxRecDepth 10000 in
-- Finite coefficient function enumeration requires deeper reduction.
/-- Every compact candidate label is intrinsically singular. -/
theorem generatedAxisE8FrameSystemCandidateLabel_singular_certificate :
    ∀ (k : Fin 270) (a : Fin 4 → ZMod 2),
      generatedAxisE8FrameSingularMask.testBit
        (generatedAxisE8FrameSystemCandidateLabel k a).val = true := by
  decide +kernel

/-- Each displayed four-column map has trivial kernel in actual intrinsic coordinates. -/
theorem generatedAxisE8FrameSystemCandidateMap_zero_certificate
    (k : Fin 270) (a : Fin 4 → ZMod 2)
    (ha : generatedAxisE8FrameSystemCandidateMap k a = 0) : a = 0 := by
  apply generatedAxisE8FrameSystemCandidateLabel_zero_certificate k a
  apply generatedAxisE8FrameLabelEquiv.injective
  change generatedAxisE8FrameLabelBits _ = generatedAxisE8FrameLabelBits 0
  rw [← generatedAxisE8FrameSystemCandidateMap_bits, ha]
  ext i
  simp [generatedAxisE8FrameLabelBits]

/-- Every displayed candidate is totally singular for the genuine intrinsic form. -/
theorem generatedAxisE8FrameSystemCandidateMap_quadratic_certificate
    (k : Fin 270) (a : Fin 4 → ZMod 2) :
    generatedAxisE8FrameQuadratic (generatedAxisE8FrameSystemCandidateMap k a) = 0 := by
  rw [generatedAxisE8FrameSystemCandidateMap_bits]
  exact (generatedAxisE8FrameSingularMask_certificate _).mp
    (generatedAxisE8FrameSystemCandidateLabel_singular_certificate k a)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
