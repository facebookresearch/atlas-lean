/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The cocode-to-lattice map and its coordinates in the actual Leech quotient.
Source: Seysen, arXiv:2002.10921v3, §§6.1–6.2.
The source frame is connected to the physical lattice, and the code/cocode
splitting and integral halves are checked on their finite generators.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Integral source map from cocode representatives to lattice vectors. -/
def leechCocodeVector (c : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => (∑ j, c j) - 4 * c i

theorem leechCocodeVector_mem (c : Fin 24 → ℤ) : leechCocodeVector c ∈ leechIntegral := by
  refine ⟨∑ j, c j, 0, ?_, ?_⟩
  · intro i
    simp [leechCocodeVector, show (4 : ZMod 4) = 0 by decide]
  · have hsum : (∑ i, leechCocodeVector c i) = 20 * (∑ i, c i) := by
      simp only [leechCocodeVector, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    change (↑(∑ i, leechCocodeVector c i) : ZMod 8) = 4 * ↑(∑ i, c i)
    rw [hsum, Int.cast_mul]
    have h20 : ((20 : ℤ) : ZMod 8) = 4 := by decide
    rw [h20]

noncomputable def leechCocodeLift : (Fin 24 → ℤ) →ₗ[ℤ] leechIntegral where
  toFun c := ⟨leechCocodeVector c, leechCocodeVector_mem c⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    simp [leechCocodeVector, Finset.sum_add_distrib]
    ring
  map_smul' a c := by
    apply Subtype.ext
    funext i
    simp [leechCocodeVector, ← Finset.mul_sum]
    ring

/-- The supplied source-frame columns as actual integral lattice elements. -/
noncomputable def leechSourceFrameLift (j : Fin 24) : leechIntegral :=
  leechExplicitCoordinateMap (leechSourceFrameCoordinates.col j)

theorem leechSourceFrameLift_vector (j : Fin 24) :
    (leechSourceFrameLift j).val = leechSourceFrameVectors.col j := by
  funext i
  have h := congrArg (fun m : Matrix (Fin 24) (Fin 24) ℤ => m i j)
    leechSourceFrameVectors_coordinates
  exact h

theorem leechSourceFrameLift_coordinates (j : Fin 24) :
    leechExplicitCoordinates (leechSourceFrameLift j) = leechSourceFrameCoordinates.col j := by
  exact (LinearEquiv.ofBijective leechExplicitCoordinateMap
    leechExplicitCoordinateMap_bijective).symm_apply_apply _

/-- Each supplied source frame vector reduces to its specified hyperbolic basis vector. -/
theorem leechSourceFrameLift_hyperbolic (j : Fin 24) :
    leechHyperbolicCoordinates (leechReduction (leechSourceFrameLift j)) = Pi.single j 1 := by
  apply leechBinaryBasisEquiv.injective
  change leechBinaryBasisEquiv
    (leechBinaryBasisEquiv.symm (leechModTwoLinearEquiv
      (leechReduction (leechSourceFrameLift j)))) = leechBinaryBasisEquiv (Pi.single j 1)
  rw [leechBinaryBasisEquiv.apply_symm_apply, leechModTwoLinearEquiv_reduce,
    leechSourceFrameLift_coordinates]
  funext i
  change (leechSourceFrameCoordinates i j : ZMod 2) =
    leechHyperbolicMatrix.mulVec (Pi.single j 1) i
  rw [Matrix.mulVec_single_one, leechSourceFrameCoordinates_parity]
  rfl

def golayCocodeInteger (j : Fin 12) (i : Fin 24) : ℤ :=
  if (golayCocodeGeneratorMasks j).testBit i.val then 1 else 0

theorem leechCocodeLift_basis (j : Fin 12) :
    leechCocodeLift (golayCocodeInteger j) = leechSourceFrameLift (Fin.natAdd 12 j) := by
  apply Subtype.ext
  rw [leechSourceFrameLift_vector]
  funext i
  change (∑ k, golayCocodeInteger j k) - 4 * golayCocodeInteger j i =
    leechSourceFrameVectors i (Fin.natAdd 12 j)
  have hnot : ¬ (Fin.natAdd 12 j).val < 12 := by simp
  simp only [leechSourceFrameVectors, hnot, dite_false]
  have hj : (⟨(Fin.natAdd 12 j).val - 12, by omega⟩ : Fin 12) = j := by
    apply Fin.ext
    simp
  rw [hj]
  simp only [leechSourceCocodeVector, golayCocodeInteger]
  congr 1
  simp [golayMaskWeight]

theorem leechCocodeLift_basis_hyperbolic (j : Fin 12) :
    leechHyperbolicCoordinates (leechReduction (leechCocodeLift (golayCocodeInteger j))) =
      Pi.single (Fin.natAdd 12 j) 1 := by
  rw [leechCocodeLift_basis, leechSourceFrameLift_hyperbolic]

noncomputable def leechCocodeClass : (Fin 24 → ZMod 2) →ₗ[ZMod 2] LeechModTwo where
  toFun c := ∑ i, c i • leechReduction (leechCocodeLift (Pi.single i 1))
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Integral cocode reduction depends only on the coefficients modulo two. -/
theorem leechCocodeClass_integer (c : Fin 24 → ℤ) :
    leechCocodeClass (integerParity c) = leechReduction (leechCocodeLift c) := by
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin 24 → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc, map_sum, map_sum]
  change (∑ i, (c i : ZMod 2) • leechReduction (leechCocodeLift (Pi.single i 1))) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul]

def golayCocodeEncoder : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun a i := ∑ j, a j * golayCocodeBit j i
  map_add' a b := by ext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' k a := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    rw [Finset.mul_sum]

def golaySyndrome : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) where
  toFun c j := ∑ i, c i * (golayGeneratorBit j i : ZMod 2)
  map_add' a b := by ext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' k a := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    rw [Finset.mul_sum]

theorem golaySyndrome_cocodeEncoder (a : Fin 12 → ZMod 2) :
    golaySyndrome (golayCocodeEncoder a) = a := by
  ext k
  change (∑ i, (∑ j, a j * golayCocodeBit j i) * (golayGeneratorBit k i : ZMod 2)) = a k
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [mul_comm (golayCocodeBit _ _) (golayGeneratorBit _ _ : ZMod 2),
    ← Finset.mul_sum, golayBasis_cocode_dual]
  simp

def golayCocodeProjection : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  golayCocodeEncoder.comp golaySyndrome

set_option maxHeartbeats 0 in
-- Verify the decomposition on the 24 coordinate generators of the binary space.
theorem golayCodeCocode_decomposition_basis : ∀ i : Fin 24,
    golayEncoder (golayDecoder (Pi.single i 1 - golayCocodeProjection (Pi.single i 1))) +
      golayCocodeProjection (Pi.single i 1) = Pi.single i 1 := by
  unfold golayCocodeProjection golayEncoder golayDecoder golaySyndrome golayCocodeEncoder
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
theorem golayCodeCocode_decomposition (c : Fin 24 → ZMod 2) :
    golayEncoder (golayDecoder (c - golayCocodeEncoder (golaySyndrome c))) +
      golayCocodeEncoder (golaySyndrome c) = c := by
  have h : golayEncoder.comp (golayDecoder.comp (LinearMap.id - golayCocodeProjection)) +
      golayCocodeProjection = LinearMap.id := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro i
    simpa only [Pi.basisFun_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply] using golayCodeCocode_decomposition_basis i
  exact congrArg (fun f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) => f c) h

def golayCodeInteger (j : Fin 12) (i : Fin 24) : ℤ := (golayGeneratorBit j i : ℤ)
def golayCodeCocodeHalf (j : Fin 12) (i : Fin 24) : ℤ :=
  (∑ k, golayCodeInteger j k) / 2 - 2 * golayCodeInteger j i

def golayCodeCocodeHalfCoefficients (j : Fin 12) : Fin 12 → ℤ :=
  -Pi.single j 1 + ((∑ i, golayCodeInteger j i) / 4) • Pi.single 11 1

set_option maxHeartbeats 0 in
-- The 12 generator congruences certify actual halves in the integral Leech lattice.
theorem golayCodeCocodeHalf_congruences : ∀ j : Fin 12,
    LeechCongruences (golayCodeCocodeHalf j) 0 (golayCodeCocodeHalfCoefficients j) := by
  unfold LeechCongruences golayCodeCocodeHalf golayCodeCocodeHalfCoefficients golayCodeInteger
  decide +kernel

set_option maxHeartbeats 0 in
-- Every generator has doubly even weight, making the displayed half integral.
theorem golayCodeCocodeHalf_double : ∀ j : Fin 12,
    2 • golayCodeCocodeHalf j = leechCocodeVector (golayCodeInteger j) := by
  unfold golayCodeCocodeHalf leechCocodeVector golayCodeInteger
  decide +kernel

noncomputable def golayCodeCocodeHalfLift (j : Fin 12) : leechIntegral :=
  ⟨golayCodeCocodeHalf j, ⟨0, golayCodeCocodeHalfCoefficients j,
    golayCodeCocodeHalf_congruences j⟩⟩

theorem leechCocodeLift_code_double (j : Fin 12) :
    leechCocodeLift (golayCodeInteger j) = 2 • golayCodeCocodeHalfLift j := by
  apply Subtype.ext
  exact (golayCodeCocodeHalf_double j).symm

theorem leechCocodeClass_code_basis (j : Fin 12) :
    leechCocodeClass (golayEncoder (Pi.single j 1)) = 0 := by
  have he : golayEncoder (Pi.single j 1) = integerParity (golayCodeInteger j) := by
    ext i
    simp [golayEncoder, Pi.single_apply, integerParity, golayCodeInteger]
  rw [he, leechCocodeClass_integer, leechCocodeLift_code_double, map_nsmul]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have hn : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [hn, zero_smul]

set_option backward.isDefEq.respectTransparency false in
theorem leechCocodeClass_code (a : Fin 12 → ZMod 2) :
    leechCocodeClass (golayEncoder a) = 0 := by
  have h : leechCocodeClass.comp golayEncoder = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.zero_apply] using
      leechCocodeClass_code_basis j
  exact congrArg (fun f : (Fin 12 → ZMod 2) →ₗ[ZMod 2] LeechModTwo => f a) h

def binaryCocodeEmbedding : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun a i := Fin.addCases (m := 12) (n := 12) (fun _ => 0) a i
  map_add' a b := by
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i <;>
      simp only [Pi.add_apply, Fin.addCases_left, Fin.addCases_right, zero_add]
  map_smul' r a := by
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i <;>
      simp only [Pi.smul_apply, RingHom.id_apply, Fin.addCases_left,
        Fin.addCases_right, smul_zero]

@[simp] theorem binaryCocodeEmbedding_left (a : Fin 12 → ZMod 2) (j : Fin 12) :
    binaryCocodeEmbedding a (Fin.castAdd 12 j) = 0 := by simp [binaryCocodeEmbedding]

@[simp] theorem binaryCocodeEmbedding_right (a : Fin 12 → ZMod 2) (j : Fin 12) :
    binaryCocodeEmbedding a (Fin.natAdd 12 j) = a j := by
  change Fin.addCases (m := 12) (n := 12) (fun _ => (0 : ZMod 2)) a
    (Fin.natAdd 12 j) = a j
  exact Fin.addCases_right j

theorem binaryCocodeEmbedding_basis (j : Fin 12) :
    binaryCocodeEmbedding (Pi.single j 1) = Pi.single (Fin.natAdd 12 j) 1 := by
  ext i
  refine Fin.addCases (m := 12) (n := 12) (fun k => ?_) (fun k => ?_) i
  · simp only [binaryCocodeEmbedding_left, Pi.single_apply, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd]
    split_ifs with h
    · omega
    · rfl
  · rw [binaryCocodeEmbedding_right]
    simp [Pi.single_apply, Fin.ext_iff]

noncomputable def leechCocodeCoordinates : (Fin 24 → ZMod 2) →ₗ[ZMod 2]
    (Fin 24 → ZMod 2) := leechHyperbolicCoordinates.toLinearMap.comp leechCocodeClass

set_option maxHeartbeats 800000 in
-- Coordinate-map extensionality traverses the certified lattice-basis equivalence.
set_option backward.isDefEq.respectTransparency false in
theorem leechCocodeCoordinates_cocodeEncoder (a : Fin 12 → ZMod 2) :
    leechCocodeCoordinates (golayCocodeEncoder a) = binaryCocodeEmbedding a := by
  have h : leechCocodeCoordinates.comp golayCocodeEncoder = binaryCocodeEmbedding := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    have he : golayCocodeEncoder (Pi.single j 1) = integerParity (golayCocodeInteger j) := by
      ext i
      change (∑ k, (Pi.single j 1 : Fin 12 → ZMod 2) k * golayCocodeBit k i) = _
      simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      simp [integerParity, golayCocodeInteger, golayCocodeBit]
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    change leechHyperbolicCoordinates (leechCocodeClass (golayCocodeEncoder (Pi.single j 1))) = _
    rw [he, leechCocodeClass_integer, leechCocodeLift_basis_hyperbolic,
      binaryCocodeEmbedding_basis]
  simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h a

theorem leechCocodeCoordinates_apply (c : Fin 24 → ZMod 2) :
    leechCocodeCoordinates c = binaryCocodeEmbedding (golaySyndrome c) := by
  have h := congrArg leechCocodeCoordinates (golayCodeCocode_decomposition c)
  rw [map_add] at h
  have hz : leechCocodeCoordinates (golayEncoder
      (golayDecoder (c - golayCocodeEncoder (golaySyndrome c)))) = 0 := by
    change leechHyperbolicCoordinates (leechCocodeClass (golayEncoder _)) = 0
    rw [leechCocodeClass_code, map_zero]
  rw [hz, zero_add, leechCocodeCoordinates_cocodeEncoder] at h
  exact h.symm

theorem leechCocodeLift_coordinates (c : Fin 24 → ℤ) :
    leechHyperbolicCoordinates (leechReduction (leechCocodeLift c)) =
      binaryCocodeEmbedding (golaySyndrome (integerParity c)) := by
  rw [← leechCocodeClass_integer]
  exact leechCocodeCoordinates_apply _
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
