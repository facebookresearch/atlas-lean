/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes

/-! Roots of the octad binary forest. Five genuine binary Ω-orbit points are reached from Ω by
explicit words in actual Conway elements; zero and four singular short classes are excluded from
the Ω orbit by genuine norm-four lattice representatives. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Masks of the five Ω-orbit roots: Ω, the octad-diagonal root, and the fifth, odd and fourth
roots. -/
def generatedAxisGlobalTwelveOctadRootMask : Fin 5 → ℕ :=
  ![2048, 4243456, 5232652, 5181440, 11747331]

/-- Masks of the excluded singular roots: zero and four short classes. -/
def generatedAxisGlobalTwelveOctadExcludedMask : Fin 5 → ℕ :=
  ![0, 3, 7, 4096, 8388608]

/-- Binary column masks of the two source permutations. -/
def generatedAxisGlobalTwelveOctadOmegaColumns : Fin 2 → Fin 24 → ℕ :=
  ![![4259837, 3150606, 7325964, 6277644, 4129584, 2550305, 4129728, 1505615, 49164, 4241412,
      51198, 2048, 987136, 4403200, 1454080, 2699264, 4259840, 196608, 4718592, 786432,
      3190784, 49152, 5181440, 12570624],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
      2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192,
      12288, 4243456, 8388608]]

set_option maxHeartbeats 16000000 in
-- Bind both displayed column lists to the certified source permutation matrices.
/-- The displayed columns are the certified binary matrices of the two permutations. -/
theorem generatedAxisGlobalTwelveOctadOmegaColumns_certificate :
    omegaOrbitBinaryMatrices 3 =
        generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveOctadOmegaColumns 0) ∧
      omegaOrbitBinaryMatrices 4 =
        generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveOctadOmegaColumns 1) := by
  decide +kernel

/-- Eighteen actual Conway letters: the sixteen octad stabilizer generators and two source
permutations. -/
def generatedAxisGlobalTwelveOctadLetter (l : Fin 18) : leechIsomSubgroup :=
  if h : l.val < 16 then generatedAxisGlobalTwelveOctadSpatial ⟨l.val, h⟩
  else if l.val = 16 then omegaOrbitIsometry 3 else omegaOrbitIsometry 4

/-- Their binary column masks. -/
def generatedAxisGlobalTwelveOctadLetterColumns (l : Fin 18) : Fin 24 → ℕ :=
  if h : l.val < 16 then generatedAxisGlobalTwelveOctadColumns ⟨l.val, h⟩
  else if l.val = 16 then generatedAxisGlobalTwelveOctadOmegaColumns 0
  else generatedAxisGlobalTwelveOctadOmegaColumns 1

/-- Every letter acts on Λ/2Λ by its column matrix. -/
theorem generatedAxisGlobalTwelveOctadLetter_binary (l : Fin 18) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveOctadLetter l)) v =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveOctadLetterColumns l) *ᵥ v := by
  by_cases h : l.val < 16
  · simp only [generatedAxisGlobalTwelveOctadLetter, generatedAxisGlobalTwelveOctadLetterColumns,
      h, ↓reduceDIte]
    exact generatedAxisGlobalTwelveOctadSpatial_binary _ v
  · by_cases h' : l.val = 16
    · simp only [generatedAxisGlobalTwelveOctadLetter, generatedAxisGlobalTwelveOctadLetterColumns,
        h', lt_self_iff_false, ↓reduceDIte, ↓reduceIte]
      change leechBinaryAction _ v = _
      rw [omegaOrbitIsometry_binary, generatedAxisGlobalTwelveOctadOmegaColumns_certificate.1]
    · simp only [generatedAxisGlobalTwelveOctadLetter, generatedAxisGlobalTwelveOctadLetterColumns,
        h, h', ↓reduceDIte, ↓reduceIte]
      change leechBinaryAction _ v = _
      rw [omegaOrbitIsometry_binary, generatedAxisGlobalTwelveOctadOmegaColumns_certificate.2]

/-- The row list of a letter. -/
def generatedAxisGlobalTwelveOctadLetterRows (l : Fin 18) : List (ℕ × ℕ) :=
  List.ofFn (fun j : Fin 24 => (j.val, generatedAxisGlobalTwelveOctadLetterColumns l j))

/-- The Conway element of a letter word; the last letter acts first. -/
def generatedAxisGlobalTwelveOctadLetterWord (w : List (Fin 18)) : Co1 :=
  (w.map (fun l => QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveOctadLetter l))).prod

/-- A letter word acts on decoded masks by the composed row lists. -/
theorem generatedAxisGlobalTwelveOctadLetterWord_action (w : List (Fin 18)) (b : ℕ) :
    co1BinaryAction (generatedAxisGlobalTwelveOctadLetterWord w)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) b) =
      monsterCo1GeometryBinaryMaskDecode
        (w.foldr (fun l acc =>
          generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadLetterRows l) acc) b) := by
  induction w with
  | nil =>
      simp only [generatedAxisGlobalTwelveOctadLetterWord, List.map_nil, List.prod_nil,
        List.foldr_nil, map_one]
      rfl
  | cons l w ih =>
      simp only [generatedAxisGlobalTwelveOctadLetterWord, List.map_cons, List.prod_cons,
        List.foldr_cons, map_mul, LinearEquiv.mul_apply] at ih ⊢
      rw [ih, generatedAxisGlobalTwelveOctadLetter_binary, generatedAxisGlobalTwelveOctadLetterRows,
        generatedAxisGlobalTwelveOctadRows_ofFn_decode]

/-- Explicit letter words reaching the five roots from Ω. -/
def generatedAxisGlobalTwelveOctadRootWord : Fin 5 → List (Fin 18) :=
  ![[], [17, 15], [17, 15, 17, 16, 15], [16, 15], [15, 17, 15, 13, 17, 15]]

set_option maxHeartbeats 16000000 in
-- Evaluate the five explicit words on the Ω mask.
/-- Each root word sends the Ω mask to the root mask. -/
theorem generatedAxisGlobalTwelveOctadRootWord_certificate : ∀ j : Fin 5,
    (generatedAxisGlobalTwelveOctadRootWord j).foldr (fun l acc =>
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadLetterRows l) acc) 2048 =
        generatedAxisGlobalTwelveOctadRootMask j := by
  decide +kernel

/-- The Ω mask decodes to the actual Ω class. -/
theorem generatedAxisGlobalTwelveOctadOmega_decode :
    monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 = toAdd (qQuotHom sourceOmegaQ) := by
  decide +kernel

/-- Every root mask is a genuine binary Ω-orbit point. -/
theorem generatedAxisGlobalTwelveOctadRootMask_mem (j : Fin 5) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveOctadRootMask j) ∈
      generatedAxisGlobalBinaryOrbit := by
  refine ⟨generatedAxisGlobalTwelveOctadLetterWord (generatedAxisGlobalTwelveOctadRootWord j), ?_⟩
  change co1BinaryAction _ (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← generatedAxisGlobalTwelveOctadOmega_decode, generatedAxisGlobalTwelveOctadLetterWord_action,
    generatedAxisGlobalTwelveOctadRootWord_certificate]

/-- The five roots as genuine binary Ω-orbit points. -/
def generatedAxisGlobalTwelveOctadRootPoint (j : Fin 5) : generatedAxisGlobalBinaryOrbit :=
  ⟨_, generatedAxisGlobalTwelveOctadRootMask_mem j⟩

/-- The root points have exactly the stated masks. -/
theorem generatedAxisGlobalTwelveOctadRootPoint_mask (j : Fin 5) :
    generatedAxisGlobalTwelveOctadMask (generatedAxisGlobalTwelveOctadRootPoint j) =
      generatedAxisGlobalTwelveOctadRootMask j := by
  apply generatedAxisGlobalTwelveOctadMask_of_decode
  · revert j
    decide +kernel
  · rfl

/-- Concrete physical integer representatives of the four short excluded classes. -/
def generatedAxisGlobalTwelveOctadShortPhysical : Fin 4 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2],
    ![0, 0, 0, 0, 4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveOctadShortCoordinates : Fin 4 → Fin 24 → ℤ :=
  ![![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-14, 3, 3, 4, 4, 2, 2, -2, 3, 2, 2, -1, 2, -1, -1, -1, 2, -1, -1, -1, -2, 0, 0, 2],
    ![0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 12000000 in
-- Check four complete lattice-coordinate, norm, and binary identities.
/-- Every displayed short vector has the stated coordinates, norm four and binary class. -/
theorem generatedAxisGlobalTwelveOctadShort_certificate : ∀ k : Fin 4,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveOctadShortCoordinates k =
      generatedAxisGlobalTwelveOctadShortPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveOctadShortPhysical k i) ^ 2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalTwelveOctadShortCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveOctadExcludedMask k.succ) := by
  decide +kernel

/-- The four short classes are excluded from the genuine binary Ω orbit. -/
theorem generatedAxisGlobalTwelveOctadShort_not_mem (k : Fin 4) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveOctadExcludedMask k.succ) ∉ generatedAxisGlobalBinaryOrbit := by
  let u := leechExplicitCoordinateMap (generatedAxisGlobalTwelveOctadShortCoordinates k)
  have hu : u.val = generatedAxisGlobalTwelveOctadShortPhysical k :=
    (generatedAxisGlobalTwelveOctadShort_certificate k).1
  have hn : leechSquareSum u.val = 32 := by
    rw [hu]
    exact (generatedAxisGlobalTwelveOctadShort_certificate k).2.1
  have hb : leechHyperbolicCoordinates (leechReduction u) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveOctadExcludedMask k.succ) := by
    rw [leechHyperbolicCoordinates_explicit]
    have hc : leechExplicitCoordinates u = generatedAxisGlobalTwelveOctadShortCoordinates k :=
      leechExplicitCoordinates.apply_symm_apply _
    rw [hc]
    exact (generatedAxisGlobalTwelveOctadShort_certificate k).2.2
  rw [← hb]
  exact generatedAxisGlobalBinary_short_excluded u hn

/-- All five excluded masks lie outside the genuine binary Ω orbit. -/
theorem generatedAxisGlobalTwelveOctadExcluded_not_mem (j : Fin 5) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveOctadExcludedMask j) ∉
      generatedAxisGlobalBinaryOrbit := by
  refine Fin.cases ?_ (fun k => generatedAxisGlobalTwelveOctadShort_not_mem k) j
  intro hz
  have h0 : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveOctadExcludedMask 0) = 0 := by
    funext i
    simp [generatedAxisGlobalTwelveOctadExcludedMask, monsterCo1GeometryBinaryMaskDecode]
  exact generatedAxisGlobalBinary_ne_zero ⟨_, hz⟩ h0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
