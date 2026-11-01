/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Half-norm on the actual Leech lattice modulo twice the lattice, in the fixed source frame.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An integral upper triangular half of the Leech basis Gram matrix. -/
def leechBasisHalfGram : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i < j then leechBasisGram i j else if i = j then leechBasisGram i i / 2 else 0

/-- The Gram matrix is the sum of this half and its transpose. -/
theorem leechBasisHalfGram_identity :
    leechBasisHalfGram + leechBasisHalfGram.transpose = leechBasisGram := by
  decide +kernel

/-- The integer half-norm polynomial in the actual lattice basis. -/
noncomputable def leechIntegralHalfNorm : QuadraticMap ℤ (Fin 24 → ℤ) ℤ :=
  leechBasisHalfGram.toBilin'.toQuadraticMap

/-- Its reduction modulo two. -/
def leechBinaryHalfGram : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  leechBasisHalfGram.map (Int.castRingHom (ZMod 2))

noncomputable def leechBinaryHalfNorm :
    QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) :=
  leechBinaryHalfGram.toBilin'.toQuadraticMap

private theorem matrix_quad_transpose {R : Type*} [CommRing R]
    (M : Matrix (Fin 24) (Fin 24) R) (x : Fin 24 → R) :
    M.transpose.toBilin' x x = M.toBilin' x x := by
  simp only [Matrix.toBilin'_apply']
  exact Matrix.dotProduct_transpose_mulVec M x x

/-- The unnormalized integer square sum is sixteen times the integral half-norm. -/
theorem leechBasis_squareSum (x : Fin 24 → ℤ) :
    leechSquareSum (leechBasisMatrix.mulVec x) = 16 * leechIntegralHalfNorm x := by
  simp only [leechSquareSum, pow_two]
  change dotProduct (leechBasisMatrix.mulVec x) (leechBasisMatrix.mulVec x) = _
  rw [← Matrix.dotProduct_transpose_mulVec leechBasisMatrix x (leechBasisMatrix.mulVec x),
    Matrix.mulVec_mulVec, leechBasisMatrix_gram]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [smul_eq_mul, ← Matrix.toBilin'_apply']
  change 8 * leechBasisGram.toBilin' x x = 16 * leechBasisHalfGram.toBilin' x x
  rw [← leechBasisHalfGram_identity, map_add]
  simp only [LinearMap.add_apply, matrix_quad_transpose]
  ring

/-- Reduction of the integral half-norm is its binary polynomial. -/
theorem leechIntegralHalfNorm_cast (x : Fin 24 → ℤ) :
    (leechIntegralHalfNorm x : ZMod 2) = leechBinaryHalfNorm (integerParity x) := by
  simp only [leechIntegralHalfNorm, leechBinaryHalfNorm,
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply, leechBinaryHalfGram,
    Matrix.map_apply, integerParity, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.cast_sum, Int.cast_mul]
  rfl

private theorem quadratic_eq_of_polar_basis
    (Q Q' : QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2))
    (hp : Q.polarBilin = Q'.polarBilin)
    (hb : ∀ i, Q (Pi.single i 1) = Q' (Pi.single i 1)) : Q = Q' := by
  apply QuadraticMap.ext
  intro x
  rw [pi_eq_sum_univ' x]
  apply Finset.sum_induction (fun i : Fin 24 => x i • Pi.single i 1)
    (fun z => Q z = Q' z)
  · intro a b ha hb
    rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q', ha, hb,
      ← QuadraticMap.polarBilin_apply_apply, hp, QuadraticMap.polarBilin_apply_apply]
  · simp
  · intro i _
    rw [QuadraticMap.map_smul Q, QuadraticMap.map_smul Q', hb]

/-- The half-norm coefficient matrix expressed in the source binary frame. -/
def leechSourceHalfGram : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  leechHyperbolicMatrix.transpose * leechBinaryHalfGram * leechHyperbolicMatrix

/-- The source basis vectors have zero binary half-norm. -/
theorem leechSourceHalfGram_diagonal : ∀ i, leechSourceHalfGram i i = 0 := by
  decide +kernel

/-- The binary polar coefficients match the fixed hyperbolic pairing. -/
theorem leechSourceHalfGram_polar : ∀ i j,
    leechSourceHalfGram i j + leechSourceHalfGram j i =
      qBeta (Pi.single i 1) (Pi.single j 1) + qBeta (Pi.single j 1) (Pi.single i 1) := by
  decide +kernel

private theorem qBeta_basis_diagonal : ∀ i : Fin 24,
    qBeta (Pi.single i 1) (Pi.single i 1) = 0 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- Transporting the explicit 24-dimensional matrix quadratic maps requires additional elaboration.
/-- The source change of basis puts the binary half-norm into plus-type hyperbolic form. -/
theorem leechSourceHalfGram_quadratic :
    leechSourceHalfGram.toBilin'.toQuadraticMap = squareQuad := by
  apply quadratic_eq_of_polar_basis
  · apply LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 24))
      (Pi.basisFun (ZMod 2) (Fin 24))
    intro i j
    simp only [Pi.basisFun_apply, QuadraticMap.polarBilin_apply_apply, squareQuad,
      LinearMap.BilinMap.polar_toQuadraticMap, Matrix.toBilin'_single]
    change leechSourceHalfGram i j + leechSourceHalfGram j i =
      qBeta (Pi.single i 1) (Pi.single j 1) + qBeta (Pi.single j 1) (Pi.single i 1)
    exact leechSourceHalfGram_polar i j
  · intro i
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_single]
    change leechSourceHalfGram i i = qBeta (Pi.single i 1) (Pi.single i 1)
    rw [leechSourceHalfGram_diagonal, qBeta_basis_diagonal]

set_option maxHeartbeats 1000000 in
-- Transporting the explicit 24-dimensional matrix quadratic maps requires additional elaboration.
/-- The binary half-norm after the supplied source-frame map is exactly `squareQuad`. -/
theorem leechBinaryHalfNorm_hyperbolic (v : Fin 24 → ZMod 2) :
    leechBinaryHalfNorm (leechHyperbolicMatrix.mulVec v) = squareQuad v := by
  have h := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) => B v v)
    (Matrix.toBilin'_comp leechBinaryHalfGram leechHyperbolicMatrix leechHyperbolicMatrix)
  change leechBinaryHalfGram.toBilin'
      (leechHyperbolicMatrix.mulVec v) (leechHyperbolicMatrix.mulVec v) =
    leechSourceHalfGram.toBilin' v v at h
  change leechBinaryHalfGram.toBilin'
      (leechHyperbolicMatrix.mulVec v) (leechHyperbolicMatrix.mulVec v) = _
  rw [h]
  have hQ := congrArg (fun Q : QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) => Q v)
    leechSourceHalfGram_quadratic
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using hQ

/-- Multiplying actual lattice coordinates by the basis matrix recovers the lattice vector. -/
theorem leechExplicitCoordinates_vector (u : leechIntegral) :
    leechBasisMatrix.mulVec (leechExplicitCoordinates u) = u.val := by
  have h := congrArg Subtype.val (leechExplicitCoordinates.symm_apply_apply u)
  exact h

/-- The quotient equivalence evaluates reduction as parity in the actual lattice basis. -/
theorem leechModTwoLinearEquiv_reduce (u : leechIntegral) :
    leechModTwoLinearEquiv (leechReduction u) = integerParity (leechExplicitCoordinates u) := by
  rfl

/-- The binary source coordinates really represent the half-norm of the underlying Leech vector. -/
theorem leechHyperbolicCoordinates_halfNorm (u : leechIntegral) :
    ((leechSquareSum u.val / 16 : ℤ) : ZMod 2) =
      squareQuad (leechHyperbolicCoordinates (leechReduction u)) := by
  rw [← leechExplicitCoordinates_vector u, leechBasis_squareSum,
    Int.mul_ediv_cancel_left _ (by decide), leechIntegralHalfNorm_cast]
  have h : leechHyperbolicMatrix.mulVec
      (leechHyperbolicCoordinates (leechReduction u)) =
      integerParity (leechExplicitCoordinates u) := by
    change leechBinaryBasisEquiv
        (leechBinaryBasisEquiv.symm (leechModTwoLinearEquiv (leechReduction u))) = _
    rw [leechBinaryBasisEquiv.apply_symm_apply, leechModTwoLinearEquiv_reduce]
  rw [← h, leechBinaryHalfNorm_hyperbolic]

/-- Every Leech isometry preserves the actual half-norm quadratic form on the binary quotient. -/
theorem leechBinaryAction_squareQuad (e : leechIsomSubgroup) (v : Fin 24 → ZMod 2) :
    squareQuad (leechBinaryAction e v) = squareQuad v := by
  obtain ⟨w, rfl⟩ := leechHyperbolicCoordinates.surjective v
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective twiceLeechIntegral w
  change squareQuad (leechHyperbolicCoordinates
    (leechModTwoAction e (leechHyperbolicCoordinates.symm
      (leechHyperbolicCoordinates (leechReduction u))))) = _
  rw [leechHyperbolicCoordinates.symm_apply_apply]
  change squareQuad (leechHyperbolicCoordinates
      (leechQuotientAut (leechIntegralAction e) (leechReduction u))) = _
  rw [leechQuotientAut_reduce, ← leechHyperbolicCoordinates_halfNorm,
    leechIntegralAction_squareSum, leechHyperbolicCoordinates_halfNorm]
  rfl

/-- The preferred lift of every norm-four Leech class is an involution in Q. -/
theorem griessShortQ_squareQuad (r : GriessShortIndex) :
    squareQuad (Multiplicative.toAdd (qQuotHom (griessShortQ r))) = 0 := by
  change squareQuad (leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r))) = 0
  rw [← leechHyperbolicCoordinates_halfNorm]
  change ((leechSquareSum (griessShortIntegral r) / 16 : ℤ) : ZMod 2) = 0
  rw [griessShortIntegral_squareSum]
  decide

/-- The canonical lift attached to a norm-four Leech line squares to the identity. -/
theorem griessShortQ_square (r : GriessShortIndex) :
    griessShortQ r * griessShortQ r = 1 := by
  apply NormalizedCocycleExtension.Extension.ext (q_square_base _)
  apply Multiplicative.toAdd.injective
  have h := griessShortQ_squareQuad r
  change qBeta (Multiplicative.toAdd (griessShortQ r).base)
      (Multiplicative.toAdd (griessShortQ r).base) = 0 at h
  change (0 + 0) + qBeta (Multiplicative.toAdd (griessShortQ r).base)
      (Multiplicative.toAdd (griessShortQ r).base) = 0
  simpa only [zero_add] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
