/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

import Mathlib.Tactic.Ring

/-!
# Finite-dimensional quantum postulates

States in `ℂⁿ`, Hermitian observables, the Born rule, unitary time evolution, the absence of a
finite-dimensional canonical commutator, and simultaneous diagonalization of commuting
observables, stated for complex matrices.

## i. Overview

This is the finite-matrix layer of ATLAS roadmap module CH36 (chemistry, core). Over a finite
index type `n`:

- a state is a vector `ψ : n → ℂ` with `star ψ ⬝ᵥ ψ = 1`;
- an observable is a Hermitian matrix (`Matrix.IsHermitian`);
- an orthonormal measurement basis is the set of columns of a unitary matrix
  `U ∈ Matrix.unitaryGroup n ℂ`, and the Born probability of outcome `i` is
  `‖(Uᴴ *ᵥ ψ) i‖ ^ 2`;
- time evolution under a time-independent Hermitian Hamiltonian `H` with the real constant
  `ħ ≠ 0` is `NormedSpace.exp (-(t / ħ) • (Complex.I • H))`, i.e. `exp (-i H t / ħ)`.
  Mathlib has no separate `Matrix.exp`: the matrix exponential is `NormedSpace.exp`, and the
  real scalar `-(t / ħ)` acts on the complex matrix `Complex.I • H`;
- the commutator of `A` and `B` is `A * B - B * A`.

The spectral theorem is Mathlib's `Matrix.IsHermitian.spectral_theorem`, the unitarity of
the exponential of a skew-adjoint element is Mathlib's
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`, and the joint-eigenspace decomposition of
commuting symmetric operators is Mathlib's
`LinearMap.IsSymmetric.directSum_isInternal_of_commute`; none is re-proved here. The general
Robertson uncertainty inequality is
`MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty.robertson` on ATLAS main (bounded
self-adjoint operators on a complex Hilbert space); it is cited, not re-proved, and not
imported here. The companion test file checks the Robertson inequality for the Pauli matrices
`σx`, `σz` in the state `![1, 0]` by explicit computation. Its variance convention, for a unit
state `ψ`, is the centred squared Euclidean norm `∑ i, ‖(A *ᵥ ψ - ⟪A ψ, ψ⟫ • ψ) i‖ ^ 2` with
`⟪A ψ, ψ⟫ = star (A *ᵥ ψ) ⬝ᵥ ψ`. For Hermitian `A`, the agreement of this variance with
MathlibExt's `variance` on unit states is a mathematical identification under the
Euclidean-space representation (coordinate vectors as elements of `EuclideanSpace ℂ n`, the
coordinate sum as the squared norm, and the dot product as the inner product); this file and
the companion test file do not prove that conversion. That check is an instance test; it does
not prove the general uncertainty principle.

`no_finite_dim_canonical_commutator` is the trace argument: the trace of a commutator vanishes,
while the trace of `i ħ I` is `n * (i ħ) ≠ 0`. As interpretation only, this is why position and
momentum must be modelled by unbounded operators with explicit domains (CH37). No statement
about unbounded operators, operator domains, or infinite-dimensional self-adjointness is made
in this file.

Reuse-verified against Mathlib/Physlib/ATLAS main; no ATLAS-50 prerequisite PR dependency.
This file imports only Mathlib. It does not depend on CH01, MF03, MF10, or any other roadmap
module's new API, and it does not duplicate the MF10 generic quantum-state API. Physlib's
operator-level counterparts, which this matrix layer neither imports nor restates, are
`QuantumMechanics.FiniteTarget.timeEvolution` (an abstract finite-dimensional Hilbert space and
the physical constant `Constants.ℏ`), `PauliMatrix.pauliMatrix`, and `LinearPMap.variance`.

## ii. Key results

- `Chemistry.Quantum.born_probabilities_sum_eq_one` : Born probabilities in an orthonormal
  measurement basis sum to `1`.
- `Chemistry.Quantum.spectral_orthonormal_eigenbasis` : a Hermitian matrix is diagonalized by
  a unitary matrix, with real eigenvalues on the diagonal.
- `Chemistry.Quantum.unitary_time_evolution` : `exp (-(t / ħ) • (I • H))` is unitary.
- `Chemistry.Quantum.no_finite_dim_canonical_commutator` : no finite matrices `X`, `P` satisfy
  `X * P - P * X = I • ħ • 1` when `ħ ≠ 0` and `0 < n`.
- `Chemistry.Quantum.simultaneous_orthonormal_eigenbasis` : commuting Hermitian matrices are
  diagonalized by one unitary matrix, with real eigenvalues.

## iii. Table of contents

- A. Born rule
- B. Spectral theorem for observables
- C. Unitary time evolution
- D. No finite-dimensional canonical commutator
- E. Simultaneous diagonalization of commuting observables

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
- ATLAS main: `MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty.robertson`.

## A. Born rule
-/

@[expose] public section

open scoped Matrix

namespace Chemistry.Quantum

/-- **Born rule normalization.** If `U` is unitary, so that its columns form an orthonormal
measurement basis, and `ψ` is a unit vector, then the Born probabilities
`‖(Uᴴ *ᵥ ψ) i‖ ^ 2` of the outcomes `i` sum to `1`. The coefficient vector `Uᴴ *ᵥ ψ` is again
a unit vector because `U * star U = 1` (`Matrix.mem_unitaryGroup_iff`). -/
lemma born_probabilities_sum_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (ψ : n → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∑ i, ‖(Uᴴ *ᵥ ψ) i‖ ^ 2 = 1 := by
  have hunit : star (Uᴴ *ᵥ ψ) ⬝ᵥ (Uᴴ *ᵥ ψ) = 1 := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hU,
      Matrix.one_mulVec, hψ]
  have hsum : ((∑ i, ‖(Uᴴ *ᵥ ψ) i‖ ^ 2 : ℝ) : ℂ) = star (Uᴴ *ᵥ ψ) ⬝ᵥ (Uᴴ *ᵥ ψ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj']
  exact_mod_cast hsum.trans hunit

/-! ## B. Spectral theorem for observables -/

/-- **Orthonormal eigenbasis of an observable.** A Hermitian matrix `A` is diagonalized by a
unitary matrix `U`, whose columns are an orthonormal eigenbasis, and its eigenvalues are real:
`Uᴴ * A * U` is the diagonal matrix of the real casts `(d i : ℂ)`. This is a direct application
of Mathlib's `Matrix.IsHermitian.spectral_theorem`, with `U = hA.eigenvectorUnitary` and
`d = hA.eigenvalues : n → ℝ`. -/
lemma spectral_orthonormal_eigenbasis {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, ∃ d : n → ℝ,
      Uᴴ * A * U = Matrix.diagonal (fun i => (d i : ℂ)) := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvectorUnitary.2, hA.eigenvalues, ?_⟩
  -- Mathlib's `Matrix.IsHermitian.spectral_theorem`:
  -- `A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U` with
  -- `U = hA.eigenvectorUnitary`; conjugating by `U` and using `star U * U = 1` gives the claim.
  have hspec := congrArg (fun M => star (hA.eigenvectorUnitary : Matrix n n ℂ) * M *
    (hA.eigenvectorUnitary : Matrix n n ℂ)) hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  rw [← Matrix.star_eq_conjTranspose, hspec, ← mul_assoc, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, mul_assoc, Unitary.coe_star_mul_self, mul_one]
  rfl

/-! ## C. Unitary time evolution -/

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

/-! ## D. No finite-dimensional canonical commutator -/

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

/-! ## E. Simultaneous diagonalization of commuting observables -/

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
