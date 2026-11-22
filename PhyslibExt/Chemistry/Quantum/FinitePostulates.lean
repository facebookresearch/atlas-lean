/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Quantum.FiniteState
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

import Mathlib.Tactic.Ring

/-!
# Finite-dimensional quantum postulates

Unitary time evolution, the absence of a finite-dimensional canonical commutator, and
simultaneous diagonalization of commuting observables, stated for complex matrices.

## i. Overview

This is the finite-matrix layer of ATLAS roadmap module CH36 (chemistry, core). Over a finite
index type `n`:

- an observable is a Hermitian matrix (`Matrix.IsHermitian`);
- time evolution under a time-independent Hermitian Hamiltonian `H` with the real constant
  `ħ ≠ 0` is `NormedSpace.exp (-(t / ħ) • (Complex.I • H))`, i.e. `exp (-i H t / ħ)`.
  Mathlib has no separate `Matrix.exp`: the matrix exponential is `NormedSpace.exp`, and the
  real scalar `-(t / ħ)` acts on the complex matrix `Complex.I • H`;
- the commutator of `A` and `B` is `A * B - B * A`.

Born probabilities use the imported `Quantum.FiniteState` API: `bornProb b ψ i` is
`‖inner ℂ (b i) ψ‖ ^ 2` for an orthonormal basis `b` and a state in
`EuclideanSpace ℂ (Fin n)`. `unitaryOrthonormalBasis U hU` is the
matrix-to-`OrthonormalBasis` bridge: the columns of the unitary matrix `U` as an orthonormal
basis (`coe_unitaryOrthonormalBasis`). `sum_bornProb_unitaryOrthonormalBasis` is Born
normalization in a unitary measurement basis, a direct corollary of `sum_bornProb_eq_one`; no
parallel matrix-coordinate Born rule is introduced. Two-state `bornProb` checks are in
`PhyslibExtTest.Chemistry.Quantum.FinitePostulates`.

The spectral theorem is Mathlib's `Matrix.IsHermitian.spectral_theorem`, used directly by
consumers. The unitarity of the exponential of a skew-adjoint element is Mathlib's
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`, and the joint-eigenspace decomposition of
commuting symmetric operators is Mathlib's
`LinearMap.IsSymmetric.directSum_isInternal_of_commute`; none is re-proved here.

`no_finite_dim_canonical_commutator` is the trace argument: the trace of a commutator vanishes,
while the trace of `i ħ I` is `n * (i ħ) ≠ 0`. As interpretation only, this is why position and
momentum must be modelled by unbounded operators with explicit domains (CH37). No statement
about unbounded operators, operator domains, infinite-dimensional self-adjointness, or the
Robertson uncertainty inequality is made in this file.

This module reuses Mathlib and the canonical finite-state API in `PhyslibExt.Quantum.FiniteState`.
Physlib's operator-level counterparts, which this matrix layer neither imports nor restates,
are `QuantumMechanics.FiniteTarget.timeEvolution` (an abstract finite-dimensional Hilbert space
and the physical constant `Constants.ℏ`) and `PauliMatrix.pauliMatrix`.

## ii. Key results

- `Chemistry.Quantum.unitaryOrthonormalBasis` : columns of a unitary matrix as an
  orthonormal basis (`coe_unitaryOrthonormalBasis`), the bridge to the canonical Born API.
- `Chemistry.Quantum.sum_bornProb_unitaryOrthonormalBasis` : Born probabilities in a unitary
  measurement basis sum to `1` for a normalized state.
- `Chemistry.Quantum.unitary_time_evolution` : `exp (-(t / ħ) • (I • H))` is unitary.
- `Chemistry.Quantum.no_finite_dim_canonical_commutator` : no finite matrices `X`, `P` satisfy
  `X * P - P * X = I • ħ • 1` when `ħ ≠ 0` and `0 < n`.
- `Chemistry.Quantum.simultaneous_orthonormal_eigenbasis` : commuting Hermitian matrices are
  diagonalized by one unitary matrix, with real eigenvalues.

## iii. Table of contents

- A. Born rule in a unitary measurement basis
- B. Unitary time evolution
- C. No finite-dimensional canonical commutator
- D. Simultaneous diagonalization of commuting observables

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 2nd ed., §1.4 (measurements,
  observables, uncertainty relations), §1.6 (canonical commutation relations), §2.1 (time
  evolution).
- M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, §2.2
  (postulates of quantum mechanics).
- Mathlib: `Matrix.IsHermitian.spectral_theorem`,
  `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`, `Matrix.mem_unitaryGroup_iff`,
  `Matrix.trace_mul_comm`, `Matrix.trace_smul`, `Matrix.trace_one`,
  `LinearMap.IsSymmetric.directSum_isInternal_of_commute`,
  `LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`.
- ATLAS: `PhyslibExt.Quantum.FiniteState` (`IsNormalized`, `bornProb`,
  `sum_bornProb_eq_one`).

## A. Born rule in a unitary measurement basis
-/

@[expose] public section

open scoped Matrix

namespace Chemistry.Quantum

/-- The squared-norm sum of a coordinate vector equals its dot product with itself. -/
private lemma ofReal_sum_norm_sq {n : ℕ} (w : Fin n → ℂ) :
    ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj']

/-- A unitary matrix preserves dot products under the `Uᴴ`-action. -/
private lemma dotProduct_conjTranspose_mulVec_of_mem_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (v : Fin n → ℂ) :
    star (Uᴴ *ᵥ v) ⬝ᵥ (Uᴴ *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hU,
    Matrix.one_mulVec]

/-- The `Uᴴ`-action of a unitary matrix preserves Euclidean norms. -/
lemma norm_toEuclideanLin_conjTranspose_of_mem_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (Uᴴ) x‖ = ‖x‖ := by
  have hsq : ‖Matrix.toEuclideanLin (Uᴴ) x‖ ^ 2 = ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ofReal_sum_norm_sq,
      ofReal_sum_norm_sq]
    show star (Uᴴ *ᵥ x.ofLp) ⬝ᵥ (Uᴴ *ᵥ x.ofLp) = star x.ofLp ⬝ᵥ x.ofLp
    exact dotProduct_conjTranspose_mulVec_of_mem_unitary U hU _
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The `Uᴴ`-action of a unitary matrix is bijective, with inverse the `U`-action. -/
lemma bijective_toEuclideanLin_conjTranspose_of_mem_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Function.Bijective ⇑(Matrix.toEuclideanLin (Uᴴ)) := by
  have hUHU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU]
  have hUUH : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hU]
  have hcomp1 : Matrix.toEuclideanLin (Uᴴ) ∘ₗ Matrix.toEuclideanLin U = LinearMap.id := by
    have h : Matrix.toLpLin 2 2 (Uᴴ) ∘ₗ Matrix.toLpLin 2 2 U = LinearMap.id := by
      rw [← Matrix.toLpLin_mul, hUHU, Matrix.toLpLin_one]
    exact h
  have hcomp2 : Matrix.toEuclideanLin U ∘ₗ Matrix.toEuclideanLin (Uᴴ) = LinearMap.id := by
    have h : Matrix.toLpLin 2 2 U ∘ₗ Matrix.toLpLin 2 2 (Uᴴ) = LinearMap.id := by
      rw [← Matrix.toLpLin_mul, hUUH, Matrix.toLpLin_one]
    exact h
  refine ⟨?_, ?_⟩
  · have hleft : Function.LeftInverse ⇑(Matrix.toEuclideanLin U) ⇑(Matrix.toEuclideanLin (Uᴴ)) :=
      fun x => by rw [← LinearMap.comp_apply, hcomp2, LinearMap.id_apply]
    exact hleft.injective
  · have hright : Function.RightInverse ⇑(Matrix.toEuclideanLin U) ⇑(Matrix.toEuclideanLin (Uᴴ)) :=
      fun x => by rw [← LinearMap.comp_apply, hcomp1, LinearMap.id_apply]
    exact hright.surjective

/-- The columns of a unitary matrix `U` as an orthonormal basis of `EuclideanSpace ℂ (Fin n)`:
the `i`-th basis vector is the `i`-th column `U *ᵥ Pi.single i 1`
(`coe_unitaryOrthonormalBasis`). The underlying linear isometry is the `Uᴴ`-action, inverted by
the `U`-action. This is the matrix-to-`OrthonormalBasis` bridge for the canonical
`Quantum.FiniteState` Born API. -/
noncomputable def unitaryOrthonormalBasis {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  OrthonormalBasis.ofRepr
    { toLinearEquiv :=
        LinearEquiv.ofBijective (Matrix.toEuclideanLin (Uᴴ))
          (bijective_toEuclideanLin_conjTranspose_of_mem_unitary U hU)
      norm_map' := norm_toEuclideanLin_conjTranspose_of_mem_unitary U hU }

/-- The `i`-th vector of `unitaryOrthonormalBasis U hU` is the `i`-th column of `U`. -/
lemma coe_unitaryOrthonormalBasis {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    unitaryOrthonormalBasis U hU i = WithLp.toLp 2 (U *ᵥ Pi.single i 1) := by
  have hUHU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU]
  rw [← (unitaryOrthonormalBasis U hU).repr_symm_single i, LinearIsometryEquiv.symm_apply_eq]
  show WithLp.toLp 2 (Pi.single i 1) =
    Matrix.toEuclideanLin (Uᴴ) (WithLp.toLp 2 (U *ᵥ Pi.single i 1))
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hUHU, Matrix.one_mulVec]

/-- **Born rule normalization in a unitary measurement basis.** If `U` is unitary, so that its
columns form the orthonormal measurement basis `unitaryOrthonormalBasis U hU`, and `ψ` is a
normalized state, then the canonical Born probabilities `bornProb` of the outcomes `i` sum to
`1`. This is `Quantum.FiniteState.sum_bornProb_eq_one` for the bridge basis. -/
lemma sum_bornProb_unitaryOrthonormalBasis {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {ψ : EuclideanSpace ℂ (Fin n)}
    (hψ : Quantum.FiniteState.IsNormalized ψ) :
    ∑ i, Quantum.FiniteState.bornProb (unitaryOrthonormalBasis U hU) ψ i = 1 :=
  Quantum.FiniteState.sum_bornProb_eq_one _ hψ

/-! ## B. Unitary time evolution -/

/-- **Unitary time evolution.** For a Hermitian Hamiltonian `H`, real time `t`, and real
`ħ ≠ 0`, the propagator `exp (-(t / ħ) • (I • H))`, i.e. `exp (-i H t / ħ)`, is unitary. The
exponent is skew-Hermitian, and Mathlib's `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`
applies; the norm used is the `L²` operator norm on matrices, under which `Matrix n n ℂ` is a
complete normed ring with continuous `star`, with the `ℚ`-algebra structure restricted from `ℂ`.
The hypothesis `ħ ≠ 0` belongs to the physical statement; the proof does not use it. -/
lemma unitary_time_evolution {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (t ħ : ℝ) (_hħ : ħ ≠ 0) :
    NormedSpace.exp (-(t / ħ) • (Complex.I • H)) ∈ Matrix.unitaryGroup n ℂ := by
  open scoped Matrix.Norms.L2Operator in
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint <| skewAdjoint.smul_mem _ <|
    hH.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I

/-! ## C. No finite-dimensional canonical commutator -/

/-- **No finite-dimensional canonical commutation relation.** For `0 < n` and `ħ ≠ 0`, no
complex `n × n` matrices `X`, `P` satisfy `X * P - P * X = I • ħ • 1`. Proof by the trace
argument: the trace of a commutator vanishes (`Matrix.trace_sub`, `Matrix.trace_mul_comm`),
while the trace of the scalar matrix is `n * (I * ħ) ≠ 0` (`Matrix.trace_smul`,
`Matrix.trace_one`). This is why position and momentum need unbounded operators with explicit
domains; no infinite-dimensional statement is made here. -/
lemma no_finite_dim_canonical_commutator {n : ℕ} (hn : 0 < n) (ħ : ℝ) (hħ : ħ ≠ 0)
    (X P : Matrix (Fin n) (Fin n) ℂ) :
    X * P - P * X ≠ Complex.I • (ħ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have htrace_comm : Matrix.trace (X * P - P * X) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have htrace_scalar :
      Matrix.trace (Complex.I • (ħ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
        n * (Complex.I * ħ) := by
    rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [h, htrace_scalar] at htrace_comm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hħ' : (ħ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hħ
  exact mul_ne_zero hn' (mul_ne_zero Complex.I_ne_zero hħ') htrace_comm

/-! ## D. Simultaneous diagonalization of commuting observables -/

/-- In a finite-dimensional inner product space with an orthonormal basis indexed by `n`, an
orthogonal internal direct sum of subspaces `V i` has an orthonormal basis indexed by `n`
whose `j`-th vector lies in `V (χ j)` for some `χ : n → ι`. -/
private lemma exists_orthonormalBasis_mem_of_isInternal {E ι n : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Fintype n] [DecidableEq ι]
    (b₀ : OrthonormalBasis n ℂ E) {V : ι → Submodule ℂ E} (hint : DirectSum.IsInternal V)
    (horth : OrthogonalFamily ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    ∃ (w : OrthonormalBasis n ℂ E) (χ : n → ι), ∀ j, w j ∈ V (χ j) := by
  have hcard : Module.finrank ℂ E = Fintype.card n := Module.finrank_eq_card_basis b₀.toBasis
  let +nondep : Fintype {i // V i ≠ ⊥} :=
    hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hint' := DirectSum.isInternal_ne_bot_iff.mpr hint
  have horth' := horth.comp (Subtype.val_injective (p := fun i => V i ≠ ⊥))
  refine ⟨(hint'.subordinateOrthonormalBasis hcard horth').reindex (Fintype.equivFin n).symm,
    fun j => (hint'.subordinateOrthonormalBasisIndex hcard (Fintype.equivFin n j) horth').1,
    fun j => ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  exact hint'.subordinateOrthonormalBasis_subordinate hcard _ horth'

/-- If the vectors of an orthonormal basis `b` of `EuclideanSpace ℂ n` are eigenvectors of `M`
with eigenvalues `μ`, then the unitary matrix whose columns are `b` diagonalizes `M`. -/
private lemma conjTranspose_toMatrix_mul_mul_eq_diagonal {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (μ : n → ℂ) (hb : ∀ j, M *ᵥ (b j).ofLp = μ j • (b j).ofLp) :
    ((EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b)ᴴ * M *
        (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b = Matrix.diagonal μ := by
  set U := (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b
  have hU : U ∈ Matrix.unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hcol : ∀ j, U *ᵥ Pi.single j 1 = (b j).ofLp := fun j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have hcol' : ∀ j, Uᴴ *ᵥ (b j).ofLp = Pi.single j 1 := fun j => by
    rw [← hcol, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mulVec]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, hb, Matrix.mulVec_smul, hcol',
    Matrix.diagonal_mulVec_single, ← Pi.single_smul', smul_eq_mul]

/-- **Simultaneous diagonalization.** Commuting Hermitian matrices `A` and `B` share an
orthonormal eigenbasis: one unitary matrix `U` diagonalizes both, with real eigenvalues. The
joint eigenspaces of their Euclidean operators are mutually orthogonal and span the space, by
Mathlib's `LinearMap.IsSymmetric.directSum_isInternal_of_commute` and
`LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`; the columns of `U` are an
orthonormal basis subordinate to that decomposition. -/
lemma simultaneous_orthonormal_eigenbasis {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, ∃ a b : n → ℝ,
      Uᴴ * A * U = Matrix.diagonal (fun i => (a i : ℂ)) ∧
        Uᴴ * B * U = Matrix.diagonal (fun i => (b i : ℂ)) := by
  have hTA : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB : (Matrix.toEuclideanLin B).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hcomm : Commute (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) := by
    change Matrix.toLpLin 2 2 A * Matrix.toLpLin 2 2 B =
      Matrix.toLpLin 2 2 B * Matrix.toLpLin 2 2 A
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLpLin_mul,
      ← Matrix.toLpLin_mul, hAB.eq]
  -- As in `directSum_isInternal_of_commute`, `(χ j).2` is the `A`- and `(χ j).1` the
  -- `B`-eigenvalue of `w j`.
  obtain ⟨w, χ, hw⟩ : ∃ (w : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (χ : n → ℂ × ℂ), ∀ j,
      w j ∈ Module.End.eigenspace (Matrix.toEuclideanLin A) (χ j).2 ⊓
        Module.End.eigenspace (Matrix.toEuclideanLin B) (χ j).1 :=
    exists_orthonormalBasis_mem_of_isInternal (EuclideanSpace.basisFun n ℂ)
      (hTA.directSum_isInternal_of_commute hTB hcomm)
      (hTA.orthogonalFamily_eigenspace_inf_eigenspace hTB)
  have hwA : ∀ j, A *ᵥ (w j).ofLp = (χ j).2 • (w j).ofLp := fun j => by
    have h := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hw j)).1
    simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp h
  have hwB : ∀ j, B *ᵥ (w j).ofLp = (χ j).1 • (w j).ofLp := fun j => by
    have h := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hw j)).2
    simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp h
  have hreal : ∀ (T : Module.End ℂ (EuclideanSpace ℂ n)), T.IsSymmetric → ∀ (μ : ℂ) j,
      w j ∈ Module.End.eigenspace T μ → ((μ.re : ℝ) : ℂ) = μ := fun T hT μ j hμ =>
    Complex.conj_eq_iff_re.mp <| hT.conj_eigenvalue_eq_self <|
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hμ, w.toBasis.ne_zero j⟩
  refine ⟨_, (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary w,
    fun j => (χ j).2.re, fun j => (χ j).1.re, ?_, ?_⟩
  · rw [conjTranspose_toMatrix_mul_mul_eq_diagonal A w _ hwA]
    congr 1
    funext j
    exact (hreal _ hTA _ j (Submodule.mem_inf.mp (hw j)).1).symm
  · rw [conjTranspose_toMatrix_mul_mul_eq_diagonal B w _ hwB]
    congr 1
    funext j
    exact (hreal _ hTB _ j (Submodule.mem_inf.mp (hw j)).2).symm

end Chemistry.Quantum
