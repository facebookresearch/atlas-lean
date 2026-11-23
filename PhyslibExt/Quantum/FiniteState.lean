/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Matrix.Spectrum

/-!

# Finite-dimensional quantum states and operators with domains

Born rule, real expectation values, a variational bound and domain-carrying operator records.

## i. Overview

A pure state of an `n`-level system is a normalized vector of `EuclideanSpace ℂ (Fin n)`, an
observable is a Hermitian matrix `A : Matrix (Fin n) (Fin n) ℂ`, and the adjoint of a matrix is its
conjugate transpose `Aᴴ` (`Matrix.conjTranspose`). The inner product is Mathlib's `inner ℂ x y`,
conjugate-linear in `x` and linear in `y`; on `ℂ`, `‖z‖` is the modulus of `z`. A matrix acts on a
state `ψ` as `WithLp.toLp 2 (A *ᵥ ψ.ofLp)`. Adjoint facts are reused from Mathlib, not reproved:
`Matrix.IsHermitian.eq` (`Aᴴ = A`), `Matrix.conjTranspose_conjTranspose` (`Aᴴᴴ = A`),
`Matrix.star_mulVec` (`star (A *ᵥ v) = star v ᵥ* Aᴴ`) and `Matrix.conjTranspose_kronecker`
(`(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`).

The Born rule and the expectation-value postulate are physical model assumptions, not consequences
of Hilbert-space algebra. They enter this file only as two definitions: `bornProb`, the probability
`‖inner ℂ (b i) ψ‖ ^ 2` of outcome `i` in the orthonormal basis `b`, and `expectationValue`, the
real part of `inner ℂ ψ (A ψ)`. The lemmas are consequences of these definitions: Born
probabilities lie in `[0, 1]`, sum to one for normalized states and are invariant under a global
phase; expectation values of Hermitian matrices are real; Kronecker products of Hermitian matrices
are Hermitian. Phase invariance is stated directly for `ψ ↦ c • ψ` with `‖c‖ = 1`; no quotient
type of rays is constructed.

Position, momentum and differential Hamiltonians are recorded as an `OperatorWithDomain`: a domain
of functions `ℝ → ℂ` and an operator defined only on that domain, following the explicit
domain-embedding pattern of `Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean`.
Only the domains and the defining formulas are recorded: no self-adjointness, no completeness, no
spectral theorem, and no claim that a formal differential expression defines an operator on all of
`ℝ → ℂ` or on `L²`. For the harmonic oscillator, the proved eigen-equation is Physlib's
`schrodingerOperator_eigenfunction` in
`Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/TISE.lean`. It is specific to the
oscillator and is not a self-adjointness result; this module cites it without importing,
restating or generalizing it.

The variational bound `inf'_le_expectationValue` is only as good as its hypothesis, an explicit
decomposition `A = U * diagonal d * Uᴴ` with `U` unitary and `d` real. This module does not prove
that every Hermitian matrix admits such a decomposition; that is Mathlib's spectral theorem
`Matrix.IsHermitian.spectral_theorem`, which `inf'_eigenvalues_le_expectationValue` uses to
discharge the hypothesis.

## ii. Key results

- `sum_bornProb_eq_one` : the Born probabilities of a normalized state sum to one.
- `bornProb_le_one` : every Born probability of a normalized state is at most one.
- `bornProb_smul` : Born probabilities are invariant under a global phase.
- `inner_mulVec_self_eq_expectationValue` : for Hermitian `A`, `inner ℂ ψ (A ψ)` is the real
  number `expectationValue A ψ`.
- `isHermitian_kronecker` : the Kronecker product of two Hermitian matrices is Hermitian.
- `momentumOperator_domain_ssubset_univ` : the momentum domain is a proper subset of `ℝ → ℂ`.
- `inf'_le_expectationValue` : the variational bound under an explicit spectral decomposition.
- `inf'_eigenvalues_le_expectationValue` : the same bound for every Hermitian matrix, with the
  decomposition supplied by Mathlib's spectral theorem.

## iii. Table of contents

- A. Normalized states
- B. Born probabilities
- C. Adjoints and expectation values
- D. Kronecker products
- E. Operators with domains
  - E.1. Position, momentum and differential Hamiltonians
  - E.2. Domain properness and membership
- F. Variational bounds

## iv. References

- M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Section 2.2 (the postulates of quantum mechanics).
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Academic Press (1980), Chapter VIII (unbounded operators).
- R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Section 4.2 (variational characterizations of eigenvalues).

-/

@[expose] public section

namespace Quantum.FiniteState

open Matrix
open scoped Kronecker

/-!

## A. Normalized states

-/

/-- A vector `ψ : EuclideanSpace ℂ (Fin n)` is normalized if its Euclidean norm is one,
`‖ψ‖ = 1`. Pure states of an `n`-level system are normalized vectors. -/
def IsNormalized {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n)) : Prop :=
  ‖ψ‖ = 1

/-- The zero vector is not normalized. -/
lemma not_isNormalized_zero (n : ℕ) : ¬IsNormalized (0 : EuclideanSpace ℂ (Fin n)) := by
  simp [IsNormalized]

/-- A normalized vector is nonzero. -/
lemma IsNormalized.ne_zero {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n)} (hψ : IsNormalized ψ) :
    ψ ≠ 0 := by
  rintro rfl
  exact not_isNormalized_zero n hψ

/-- Multiplying a normalized vector by a unit-modulus scalar gives a normalized vector. -/
lemma IsNormalized.smul {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n)} (hψ : IsNormalized ψ) {c : ℂ}
    (hc : ‖c‖ = 1) : IsNormalized (c • ψ) := by
  rw [IsNormalized, norm_smul, hc, hψ, one_mul]

/-!

## B. Born probabilities

-/

/-- The Born probability of outcome `i` when the state `ψ` is measured in the orthonormal basis
`b`: the squared modulus `‖inner ℂ (b i) ψ‖ ^ 2` of the amplitude `inner ℂ (b i) ψ`. This is the
Born rule, a physical postulate taken as a definition. -/
noncomputable def bornProb {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) : ℝ :=
  ‖inner ℂ (b i) ψ‖ ^ 2

/-- Born probabilities are nonnegative. -/
lemma bornProb_nonneg {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) : 0 ≤ bornProb b ψ i :=
  sq_nonneg _

/-- Parseval's identity: the Born probabilities of any vector sum to its squared norm. -/
lemma sum_bornProb {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (ψ : EuclideanSpace ℂ (Fin n)) : ∑ i, bornProb b ψ i = ‖ψ‖ ^ 2 :=
  b.sum_sq_norm_inner_right ψ

/-- The Born probabilities of a normalized state sum to one. -/
lemma sum_bornProb_eq_one {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    {ψ : EuclideanSpace ℂ (Fin n)} (hψ : IsNormalized ψ) : ∑ i, bornProb b ψ i = 1 := by
  rw [sum_bornProb, hψ, one_pow]

/-- Every Born probability of a normalized state is at most one. -/
lemma bornProb_le_one {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    {ψ : EuclideanSpace ℂ (Fin n)} (hψ : IsNormalized ψ) (i : Fin n) : bornProb b ψ i ≤ 1 := by
  rw [← sum_bornProb_eq_one b hψ]
  exact Finset.single_le_sum (fun j _ => bornProb_nonneg b ψ j) (Finset.mem_univ i)

/-- Global phase invariance: multiplying a state by a unit-modulus scalar `c` leaves every Born
probability unchanged. -/
lemma bornProb_smul {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (ψ : EuclideanSpace ℂ (Fin n)) {c : ℂ} (hc : ‖c‖ = 1) (i : Fin n) :
    bornProb b (c • ψ) i = bornProb b ψ i := by
  rw [bornProb, bornProb, inner_smul_right, norm_mul, hc, one_mul]

/-!

## C. Adjoints and expectation values

-/

/-- The conjugate transpose is the adjoint for the inner product:
`inner ℂ (A x) y = inner ℂ x (Aᴴ y)`. -/
lemma inner_mulVec_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (WithLp.toLp 2 (A *ᵥ x.ofLp)) y = inner ℂ x (WithLp.toLp 2 (Aᴴ *ᵥ y.ofLp)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, WithLp.ofLp_toLp, star_mulVec, dotProduct_comm, ← dotProduct_mulVec,
    dotProduct_comm]

/-- A Hermitian matrix is its own adjoint: `inner ℂ (A x) y = inner ℂ x (A y)`. This combines
`inner_mulVec_left` with `Aᴴ = A` (`Matrix.IsHermitian.eq`). -/
lemma inner_mulVec_left_of_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (WithLp.toLp 2 (A *ᵥ x.ofLp)) y = inner ℂ x (WithLp.toLp 2 (A *ᵥ y.ofLp)) := by
  rw [inner_mulVec_left, hA.eq]

/-- The expectation value of the observable `A` in the state `ψ`: the real part of
`inner ℂ ψ (A ψ)`. This is the expectation-value postulate, taken as a definition. For Hermitian
`A` the inner product is real (`inner_mulVec_self_eq_expectationValue`), so taking the real part
discards nothing. -/
noncomputable def expectationValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  (inner ℂ ψ (WithLp.toLp 2 (A *ᵥ ψ.ofLp))).re

/-- For a Hermitian matrix `A`, the imaginary part of `inner ℂ ψ (A ψ)` is zero. -/
lemma im_inner_mulVec_self_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (ψ : EuclideanSpace ℂ (Fin n)) : (inner ℂ ψ (WithLp.toLp 2 (A *ᵥ ψ.ofLp))).im = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct_comm]
  exact hA.im_star_dotProduct_mulVec_self ψ.ofLp

/-- For a Hermitian matrix `A`, `inner ℂ ψ (A ψ)` is the real number `expectationValue A ψ`. -/
lemma inner_mulVec_self_eq_expectationValue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin n)) :
    inner ℂ ψ (WithLp.toLp 2 (A *ᵥ ψ.ofLp)) = (expectationValue A ψ : ℂ) :=
  Complex.ext rfl (by rw [Complex.ofReal_im, im_inner_mulVec_self_eq_zero hA])

/-!

## D. Kronecker products

-/

/-- The Kronecker product of two Hermitian matrices is Hermitian. The proof uses Mathlib's
`Matrix.conjTranspose_kronecker`, `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`. -/
lemma isHermitian_kronecker {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).IsHermitian := by
  change (kroneckerMap (· * ·) A B)ᴴ = kroneckerMap (· * ·) A B
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-!

## E. Operators with domains

-/

/-- An operator on functions `ℝ → ℂ` together with its domain: `domain` is the set of functions on
which the operator is defined, and `op` is defined only on elements of `domain`, as a function out
of the subtype. An unbounded operator is such a pair, never an endomorphism of the whole function
space. No linearity, continuity, density of the domain or self-adjointness is assumed or
claimed. -/
structure OperatorWithDomain where
  /-- The domain: the functions `ℝ → ℂ` on which the operator is defined. -/
  domain : Set (ℝ → ℂ)
  /-- The action of the operator on elements of its domain. -/
  op : domain → ℝ → ℂ

/-- The embedding of the domain of `T` into the function space `ℝ → ℂ`. -/
def OperatorWithDomain.embedding (T : OperatorWithDomain) : T.domain → ℝ → ℂ :=
  Subtype.val

/-- The domain embedding is injective. -/
lemma OperatorWithDomain.embedding_injective (T : OperatorWithDomain) :
    Function.Injective T.embedding :=
  Subtype.val_injective

/-!

### E.1. Position, momentum and differential Hamiltonians

-/

/-- The position operator `f ↦ (x ↦ x * f x)`, with domain all functions `ℝ → ℂ`. Multiplication
by the coordinate is defined for every function, so this totality is a statement about the function
space `ℝ → ℂ`; the `L²` domain of the position operator is not described here. -/
def positionOperator : OperatorWithDomain where
  domain := Set.univ
  op f x := x * (f : ℝ → ℂ) x

/-- The momentum operator `f ↦ -i f'` (units with `ħ = 1`), with domain the functions `ℝ → ℂ`
that are differentiable at every point of `ℝ`. -/
noncomputable def momentumOperator : OperatorWithDomain where
  domain := {f | Differentiable ℝ f}
  op f x := -Complex.I * deriv (f : ℝ → ℂ) x

/-- The differential Hamiltonian `f ↦ -f'' + V f` for a potential `V : ℝ → ℂ` (units with `ħ = 1`
and mass `1 / 2`), with domain the twice continuously differentiable functions `ℝ → ℂ`,
`ContDiff ℝ 2 f`. -/
noncomputable def differentialHamiltonian (V : ℝ → ℂ) : OperatorWithDomain where
  domain := {f | ContDiff ℝ 2 f}
  op f x := -deriv (deriv (f : ℝ → ℂ)) x + V x * (f : ℝ → ℂ) x

/-!

### E.2. Domain properness and membership

-/

/-- The domain of the position operator is all of `ℝ → ℂ`. -/
lemma positionOperator_domain : positionOperator.domain = Set.univ :=
  rfl

/-- The function `x ↦ |x|` is not in the domain of the momentum operator: it is not differentiable
at `0` (`not_differentiableAt_abs_zero`). -/
lemma abs_notMem_momentumOperator_domain :
    (fun x : ℝ => ((|x| : ℝ) : ℂ)) ∉ momentumOperator.domain := by
  intro h
  refine not_differentiableAt_abs_zero ?_
  convert (Complex.reCLM.differentiable.comp h) 0 using 1
  funext x
  simp

/-- The domain of the momentum operator is a proper subset of `ℝ → ℂ`. -/
lemma momentumOperator_domain_ssubset_univ : momentumOperator.domain ⊂ Set.univ :=
  Set.ssubset_univ_iff.mpr fun h =>
    abs_notMem_momentumOperator_domain (h ▸ Set.mem_univ _)

/-- The constant function `1` is in the domain of the momentum operator. -/
lemma const_one_mem_momentumOperator_domain :
    (fun _ : ℝ => (1 : ℂ)) ∈ momentumOperator.domain :=
  differentiable_const 1

/-- The constant function `1` is in the domain of the differential Hamiltonian, for every
potential `V`. -/
lemma const_one_mem_differentialHamiltonian_domain (V : ℝ → ℂ) :
    (fun _ : ℝ => (1 : ℂ)) ∈ (differentialHamiltonian V).domain :=
  (contDiff_const : ContDiff ℝ 2 fun _ : ℝ => (1 : ℂ))

/-!

## F. Variational bounds

-/

/-- Variational bound: if `A = U * diagonal d * Uᴴ` with `U` unitary and `d` real, then for every
normalized state `ψ` the expectation value of `A` is at least the smallest entry
`Finset.univ.inf' Finset.univ_nonempty d` of `d`. The decomposition is an explicit hypothesis; such
an `A` is Hermitian (`Matrix.isHermitian_mul_mul_conjTranspose`), and Mathlib's spectral theorem
provides the decomposition for every Hermitian matrix (`inf'_eigenvalues_le_expectationValue`). -/
lemma inf'_le_expectationValue {n : ℕ} [NeZero n] {A U : Matrix (Fin n) (Fin n) ℂ}
    {d : Fin n → ℝ} (hU : U ∈ unitaryGroup (Fin n) ℂ)
    (hA : A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ) {ψ : EuclideanSpace ℂ (Fin n)}
    (hψ : IsNormalized ψ) :
    Finset.univ.inf' Finset.univ_nonempty d ≤ expectationValue A ψ := by
  set φ : Fin n → ℂ := Uᴴ *ᵥ ψ.ofLp with hφ
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff.mp hU
  have hstar : star ψ.ofLp ᵥ* U = star φ := by
    rw [hφ, star_mulVec, conjTranspose_conjTranspose]
  have hsq : ∀ w : Fin n → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.ofReal_pow, ← Complex.conj_mul', starRingEnd_apply]
  have hexp : expectationValue A ψ = ∑ i, d i * ‖φ i‖ ^ 2 := by
    have key : star ψ.ofLp ⬝ᵥ (A *ᵥ ψ.ofLp) = ∑ i, ((d i * ‖φ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hA, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hstar, ← hφ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mulVec_diagonal, Pi.star_apply, Complex.ofReal_mul, Complex.ofReal_pow,
        ← Complex.conj_mul', starRingEnd_apply]
      ring
    rw [expectationValue, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      dotProduct_comm, key, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hnorm : ∑ i, ‖φ i‖ ^ 2 = 1 := by
    have key : star φ ⬝ᵥ φ = star ψ.ofLp ⬝ᵥ ψ.ofLp := by
      rw [← hstar, ← dotProduct_mulVec, hφ, mulVec_mulVec, hUU, one_mulVec]
    rw [hsq, hsq] at key
    rw [Complex.ofReal_injective key, ← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  rw [hexp]
  calc Finset.univ.inf' Finset.univ_nonempty d
      = Finset.univ.inf' Finset.univ_nonempty d * ∑ i, ‖φ i‖ ^ 2 := by rw [hnorm, mul_one]
    _ = ∑ i, Finset.univ.inf' Finset.univ_nonempty d * ‖φ i‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i, d i * ‖φ i‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (Finset.inf'_le d (Finset.mem_univ i)) (sq_nonneg _)

/-- For every Hermitian matrix `A` and normalized state `ψ`, the expectation value of `A` is at
least the smallest eigenvalue of `A`. The spectral hypothesis of `inf'_le_expectationValue` is
discharged by Mathlib's spectral theorem `Matrix.IsHermitian.spectral_theorem`. -/
lemma inf'_eigenvalues_le_expectationValue {n : ℕ} [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) {ψ : EuclideanSpace ℂ (Fin n)} (hψ : IsNormalized ψ) :
    Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues ≤ expectationValue A ψ := by
  refine inf'_le_expectationValue hA.eigenvectorUnitary.2 (hA.spectral_theorem.trans ?_) hψ
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  rfl

end Quantum.FiniteState
