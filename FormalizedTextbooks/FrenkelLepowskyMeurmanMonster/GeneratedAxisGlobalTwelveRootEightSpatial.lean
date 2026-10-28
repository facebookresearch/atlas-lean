/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightSpatialData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTransport
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReductionData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100PointMover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100MateOrientation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PositiveRootStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! The four root-eight forest letters as genuine Leech isometries, and their binary actions.

Each letter is the conjugate `T⁻¹ g T` of an original canonical stabilizer generator `g` by
the literal canonical transport `T` of the root-eight flag: the two reduced Mathieu words, the
point mover and the mate orientation. Integral basis certificates for every literal factor give
the exact action on Λ/2Λ, which is the forest column data. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- An integral basis certificate: the isometry acts on basis coordinates by `C`. -/
def rootEightSpatialBasisCert (e : leechIsomSubgroup)
    (C : Matrix (Fin 24) (Fin 24) ℤ) : Prop :=
  ∀ z : Fin 24 → ℤ, e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ (C *ᵥ z))

/-- A physical integer matrix action with a basis transport certificate gives a certificate. -/
theorem rootEightSpatialBasisCert_of_physical (e : leechIsomSubgroup)
    (M C : Matrix (Fin 24) (Fin 24) ℤ)
    (he : ∀ u, e.val (leechCoordinateEmbedding u) = leechCoordinateEmbedding (M *ᵥ u))
    (hc : M * leechBasisMatrix = leechBasisMatrix * C) :
    rootEightSpatialBasisCert e C := by
  intro z
  rw [he, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]

/-- Certificates compose along products of isometries. -/
theorem rootEightSpatialBasisCert_mul {e f : leechIsomSubgroup}
    {C D : Matrix (Fin 24) (Fin 24) ℤ} (he : rootEightSpatialBasisCert e C)
    (hf : rootEightSpatialBasisCert f D) :
    rootEightSpatialBasisCert (e * f) (C * D) := by
  intro z
  change e.val (f.val _) = _
  rw [hf, he, Matrix.mulVec_mulVec z C D]

/-- A right inverse integral matrix certifies the inverse isometry. -/
theorem rootEightSpatialBasisCert_inv {e : leechIsomSubgroup}
    {C D : Matrix (Fin 24) (Fin 24) ℤ} (he : rootEightSpatialBasisCert e C)
    (hCD : C * D = 1) : rootEightSpatialBasisCert e⁻¹ D := by
  intro z
  have h := he (D *ᵥ z)
  rw [Matrix.mulVec_mulVec z C D, hCD, Matrix.one_mulVec] at h
  change e.val.symm _ = _
  rw [← h, LinearEquiv.symm_apply_apply]

/-- A certificate determines the exact binary action on Λ/2Λ. -/
theorem rootEightSpatialBasisCert_binary {e : leechIsomSubgroup}
    {C : Matrix (Fin 24) (Fin 24) ℤ} (he : rootEightSpatialBasisCert e C)
    (v : Fin 24 → ZMod 2) :
    leechBinaryAction e v =
      (leechHyperbolicInverse * C.map (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix) *ᵥ v :=
  leechBinaryAction_of_basis_certificate e C he v

/-- A coordinate permutation acts by its physical permutation matrix. -/
theorem rootEightSpatialPermutation_embedding (p : golayAutomorphismSubgroup)
    (a : Fin 24 → Fin 24) (ha : ∀ j, p.val j = a j) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry p).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (rootEightSpatialPermutationPhysical a *ᵥ u) := by
  have hp : ∀ i j : Fin 24, rootEightSpatialPermutationPhysical a i j =
      if p.val.symm i = j then 1 else 0 := by
    intro i j
    change (if a j = i then (1 : ℤ) else 0) = _
    rw [← ha]
    have he : p.val j = i ↔ p.val.symm i = j := (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- A Golay sign acts by its physical diagonal sign matrix. -/
theorem rootEightSpatialSign_embedding (d : golayCode) (s : Fin 24 → ℤ)
    (hs : ∀ i, (if d.val i = 0 then (1 : ℤ) else -1) = s i) (u : Fin 24 → ℤ) :
    (golaySignIsometry d).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (Matrix.diagonal s *ᵥ u) := by
  change golayRealSign d.val (leechCoordinateEmbedding u) = _
  rw [golayRealSign_embedding]
  congr 1
  ext i
  rw [Matrix.mulVec_diagonal, ← hs i]
  simp only [golayIntegerSign]
  split_ifs <;> ring

/-- The ten literal permutation factors. -/
def rootEightSpatialPermutation : Fin 10 → golayAutomorphismSubgroup :=
  ![generatedFifthRootEightCanonicalPermutation 0, generatedFifthRootEightCanonicalPermutation 1,
    generatedFifthRootEightCanonicalPermutation 2, generatedRootEightMathieuReducedGenerator 0,
    generatedRootEightMathieuReducedGenerator 1, leechNormSixHS100PointMoverPermutation 0,
    leechNormSixHS100PointMoverPermutation 1, leechNormSixHS100PointMoverPermutation 2,
    leechNormSixHS100PointMoverPermutation 3, leechNormSixHS100MatePermutation]

set_option maxHeartbeats 16000000 in
-- Evaluate every coordinate of the ten literal permutation words.
set_option maxRecDepth 100000 in
/-- The forward arrays are exactly the literal permutation factors. -/
theorem rootEightSpatialPermutation_forward : ∀ k : Fin 10, ∀ j : Fin 24,
    (rootEightSpatialPermutation k).val j = rootEightSpatialPermutationArray k j := by
  decide +kernel

/-- The six literal sign factors. -/
def rootEightSpatialSign : Fin 6 → golayCode :=
  ![golayCodeLabelEquiv (generatedFifthRootEightCanonicalSignLabels 0),
    golayCodeLabelEquiv (generatedFifthRootEightCanonicalSignLabels 1),
    golayCodeLabelEquiv (generatedFifthRootEightCanonicalSignLabels 2),
    leechNormSixHS100PointMoverSign 1, leechNormSixHS100PointMoverSign 2816, leechRootNegationCode]

set_option maxHeartbeats 16000000 in
-- Evaluate every coordinate of the six literal sign codewords.
set_option maxRecDepth 100000 in
/-- The sign vectors are exactly the literal Golay sign factors. -/
theorem rootEightSpatialSign_vector : ∀ k : Fin 6, ∀ i : Fin 24,
    (if (rootEightSpatialSign k).val i = 0 then (1 : ℤ) else -1) =
      rootEightSpatialSignVector k i := by
  decide +kernel

/-- Each permutation factor has its integral basis certificate. -/
theorem rootEightSpatialPermutation_cert (k : Fin 10) :
    rootEightSpatialBasisCert
      (golayPermutationIsometry (rootEightSpatialPermutation k))
      (rootEightSpatialPermutationIntegral k) :=
  rootEightSpatialBasisCert_of_physical _ _ _
    (rootEightSpatialPermutation_embedding _ _
      (rootEightSpatialPermutation_forward k))
    (rootEightSpatialPermutation_integral k)

/-- Each sign factor has its integral basis certificate. -/
theorem rootEightSpatialSign_cert (k : Fin 6) :
    rootEightSpatialBasisCert
      (golaySignIsometry (rootEightSpatialSign k))
      (rootEightSpatialSignIntegral k) :=
  rootEightSpatialBasisCert_of_physical _ _ _
    (rootEightSpatialSign_embedding _ _
      (rootEightSpatialSign_vector k))
    (rootEightSpatialSign_integral k)

/-- The three-bases factor has its integral basis certificate. -/
theorem rootEightSpatialXi_cert :
    rootEightSpatialBasisCert co1XiIsometry co1XiBasisMatrix :=
  co1Xi_embedding_basis

/-- The canonical transport has its integral basis certificate. -/
theorem rootEightSpatialTransport_cert :
    rootEightSpatialBasisCert generatedFifthRootEightCanonicalTransport
      rootEightSpatialTransportIntegral := by
  have s0 := rootEightSpatialSign_cert 0
  have s1 := rootEightSpatialSign_cert 1
  have s2 := rootEightSpatialSign_cert 2
  have p0 := rootEightSpatialPermutation_cert 0
  have p1 := rootEightSpatialPermutation_cert 1
  have p2 := rootEightSpatialPermutation_cert 2
  dsimp only [rootEightSpatialSign, Matrix.cons_val] at s0 s1 s2
  dsimp only [rootEightSpatialPermutation, Matrix.cons_val] at p0 p1 p2
  have hx := rootEightSpatialXi_cert
  have m0 := rootEightSpatialBasisCert_mul s0 p0
  have m1 := rootEightSpatialBasisCert_mul s1 p1
  have m2 := rootEightSpatialBasisCert_mul s2 p2
  have h1 := rootEightSpatialBasisCert_mul (rootEightSpatialBasisCert_mul m2 hx) hx
  have h2 := rootEightSpatialBasisCert_mul (rootEightSpatialBasisCert_mul h1 m1) hx
  have h3 := rootEightSpatialBasisCert_mul h2 m0
  rw [rootEightSpatialTransportIntegral_eq]
  simp only [generatedFifthRootEightCanonicalTransport, generatedFifthRootEightCanonicalMonomial]
  exact h3

/-- The inverse canonical transport has its integral basis certificate. -/
theorem rootEightSpatialTransportInverse_cert :
    rootEightSpatialBasisCert generatedFifthRootEightCanonicalTransport⁻¹
      rootEightSpatialTransportInverseIntegral :=
  rootEightSpatialBasisCert_inv rootEightSpatialTransport_cert
    rootEightSpatialTransportIntegral_inverse

/-- The four original canonical stabilizer generators: the two reduced Mathieu words, the
point mover and the mate orientation. -/
def rootEightSpatialCanonicalGenerator : Fin 4 → leechIsomSubgroup :=
  ![golayPermutationIsometry (generatedRootEightMathieuReducedGenerator 0),
    golayPermutationIsometry (generatedRootEightMathieuReducedGenerator 1),
    leechNormSixHS100PointMover, leechNormSixHS100MateOrientation]

/-- The four root-eight forest letters: canonical-transport conjugates of the originals. -/
def rootEightForestIsometry (k : Fin 4) : leechIsomSubgroup :=
  generatedFifthRootEightCanonicalTransport⁻¹ * rootEightSpatialCanonicalGenerator k *
    generatedFifthRootEightCanonicalTransport

/-- Each canonical generator has its integral basis certificate. -/
theorem rootEightSpatialCanonical_cert (k : Fin 4) :
    rootEightSpatialBasisCert (rootEightSpatialCanonicalGenerator k)
      (rootEightSpatialCanonicalIntegral k) := by
  obtain ⟨h0, h1, h2, h3⟩ := rootEightSpatialCanonicalIntegral_eq
  have hp := rootEightSpatialPermutation_cert
  have hs := rootEightSpatialSign_cert
  have hx := rootEightSpatialXi_cert
  fin_cases k
  · change rootEightSpatialBasisCert
      (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator 0))
      (rootEightSpatialCanonicalIntegral 0)
    rw [h0]
    exact hp 3
  · change rootEightSpatialBasisCert
      (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator 1))
      (rootEightSpatialCanonicalIntegral 1)
    rw [h1]
    exact hp 4
  · change rootEightSpatialBasisCert leechNormSixHS100PointMover
      (rootEightSpatialCanonicalIntegral 2)
    rw [h2, leechNormSixHS100PointMover_literal_word]
    have a1 := rootEightSpatialBasisCert_mul (rootEightSpatialBasisCert_mul (hp 8) (hs 3)) (hp 7)
    have a2 := rootEightSpatialBasisCert_mul (rootEightSpatialBasisCert_mul a1 hx) (hp 6)
    have a3 := rootEightSpatialBasisCert_mul (rootEightSpatialBasisCert_mul a2 hx) hx
    exact rootEightSpatialBasisCert_mul (rootEightSpatialBasisCert_mul a3 (hs 4)) (hp 5)
  · change rootEightSpatialBasisCert leechNormSixHS100MateOrientation
      (rootEightSpatialCanonicalIntegral 3)
    rw [h3]
    exact rootEightSpatialBasisCert_mul (hs 5) (hp 9)

/-- Each forest letter has its integral basis certificate. -/
theorem rootEightSpatialLetter_cert (k : Fin 4) :
    rootEightSpatialBasisCert (rootEightForestIsometry k) (rootEightSpatialLetterIntegral k) := by
  have h := rootEightSpatialBasisCert_mul rootEightSpatialTransportInverse_cert
    (rootEightSpatialCanonical_cert k)
  rw [rootEightSpatialLetterIntegral_eq]
  exact rootEightSpatialBasisCert_mul h rootEightSpatialTransport_cert

/-- The forest letters act on Λ/2Λ exactly by the forest column data. -/
theorem rootEightForestIsometry_binary (k : Fin 4) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (rootEightForestIsometry k)) v =
      generatedAxisGlobalMaskColumnMatrix (rootEightForestColumns k) *ᵥ v := by
  change leechBinaryAction _ v = _
  rw [rootEightSpatialBasisCert_binary (rootEightSpatialLetter_cert k),
    rootEightSpatialLetter_columns]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
