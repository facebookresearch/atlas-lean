/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multistationarity requires a positive circuit (Thomas' rule)

For a real `n × n` matrix `A`, the interaction graph `G(A)` has vertices `1, …, n` and an edge
`j → i` exactly when `A_{ij} ≠ 0`, with the sign of `A_{ij}`. A circuit is positive if the
product of the signs of its edges is `+1`. For `I ⊆ {1, …, n}`, `τ_I A` changes the sign of the
entries `A_{ij}` with `i ∈ I`, and for a permutation `σ`, `σ A` is the left product
`(σ⁻¹).permMatrix ℝ * A` (entries `(σ A)_{ij} = A_{σ⁻¹(i), j}`), so that `G(σ A)` replaces each
edge `j → i` by `j → σ(i)`.

Let `Ω = ∏_i Ω_i ⊆ ℝ^n` be a product of open intervals, and let `F : Ω → ℝ^n` be differentiable,
with Jacobian matrix `J(a) = (∂F_i/∂x_j (a))`. A zero `a` of `F` is nondegenerate if
`det J(a) ≠ 0`.

**Theorem 1** (Soulé 2003). If `Ω` is open and `F` has at least two nondegenerate zeros in `Ω`,
then for every `I ⊆ {1, …, n}` and every permutation `σ` there is `a ∈ Ω` such that the
interaction graph of `σ τ_I J(a)` has a positive circuit. In particular (`I = ∅`, `σ = id`),
`G(a)` has a positive circuit for some `a ∈ Ω` (Thomas' conjecture).

**Theorem 1′** (Soulé 2003). If, for every `a ∈ Ω`, all principal minors of `-J(a)` are
nonnegative, then `F` has at most one nondegenerate zero in `Ω`.

Circuits are stated with distinct vertices (the circuits of permutation cycles used in the
source's proof); since the source's circuits may repeat vertices, this is the stronger reading.
The intervals `Ω_i` may be unbounded. The source proves Theorem 1′ through the univalence theorem
of Gale and Nikaido and a degree argument.

Sources: C. Soulé, "Graphic requirements for multistationarity", ComPlexUs 1 (2003) 123–133,
Sections 1–3, Theorems 1 and 1′ (arXiv:q-bio/0403033); D. Gale, H. Nikaido, "The Jacobian matrix
and global univalence of mappings", Math. Ann. 159 (1965) 81–93.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Biophysics.ThomasRuleWanted

variable {n : ℕ}

/-- `τ_I A`: change the sign of every entry `A_{ij}` with `i ∈ I`. -/
def tauSign (I : Finset (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ∈ I then -A i j else A i j

/-- `σ A`: the left product `(σ⁻¹).permMatrix ℝ * A` under Mathlib's permutation-matrix convention,
with entries `(permRows σ A) i j = A (σ⁻¹ i) j` (equivalently `(σ A)_{σ(i) j} = A_{ij}`), so that
its interaction graph replaces each edge `j → i` of `G(A)` by `j → σ(i)`. -/
def permRows (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A (σ.symm i) j

/-- The interaction graph of `A` has a positive circuit: there are distinct vertices
`v_0, …, v_k` such that each `v_m → v_{m+1}` (indices modulo `k + 1`) is an edge, that is
`A_{v_{m+1} v_m} ≠ 0`, and the product of the signs of these edges is `+1`; equivalently the
product of the entries `A_{v_{m+1} v_m}` is positive. -/
def HasPositiveCircuit (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (k : ℕ) (v : Fin (k + 1) → Fin n), Function.Injective v ∧
    0 < ∏ m, A (v (m + 1)) (v m)

/-- The Jacobian matrix `J(a)_{ij} = ∂F_i/∂x_j (a)` of `F : ℝ^n → ℝ^n` at a point `a` where `F` is
differentiable (`fderiv` is `0` elsewhere). -/
noncomputable def jacobian (F : (Fin n → ℝ) → Fin n → ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ F a (Pi.single j 1) i

/-- `a` is a nondegenerate zero of `F`: `F a = 0` and `det J(a) ≠ 0`. -/
def IsNondegenerateZero (F : (Fin n → ℝ) → Fin n → ℝ) (a : Fin n → ℝ) : Prop :=
  F a = 0 ∧ (jacobian F a).det ≠ 0

/-- **Thomas' rule** (Soulé 2003, Theorem 1). Let `Ω = ∏_i Ω_i ⊆ ℝ^n` where each `Ω_i` is an
open interval of `ℝ` (open and order-connected, possibly unbounded), and let `F : ℝ^n → ℝ^n` be
differentiable at every point of `Ω`. If `F` has two distinct nondegenerate zeros `a ≠ b` in `Ω`
(`F a = F b = 0`, `det J(a) ≠ 0`, `det J(b) ≠ 0`), then for every `I ⊆ {1, …, n}` and every
permutation `σ` there is `x ∈ Ω` such that the interaction graph of `σ τ_I J(x)` has a positive
circuit (with distinct vertices).

Source: C. Soulé, ComPlexUs 1 (2003) 123–133, Theorem 1. -/
theorem_wanted exists_hasPositiveCircuit (Ωi : Fin n → Set ℝ) (hopen : ∀ i, IsOpen (Ωi i))
    (hconn : ∀ i, (Ωi i).OrdConnected) {F : (Fin n → ℝ) → Fin n → ℝ}
    (hF : ∀ x ∈ Set.univ.pi Ωi, DifferentiableAt ℝ F x) {a b : Fin n → ℝ}
    (ha : a ∈ Set.univ.pi Ωi) (hb : b ∈ Set.univ.pi Ωi) (hab : a ≠ b)
    (ha0 : IsNondegenerateZero F a) (hb0 : IsNondegenerateZero F b)
    (I : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    ∃ x ∈ Set.univ.pi Ωi, HasPositiveCircuit (permRows σ (tauSign I (jacobian F x)))

/-- **Nonnegative principal minors force at most one nondegenerate zero** (Soulé 2003,
Theorem 1′). Let `Ω = ∏_i Ω_i` be a product of open intervals and let `F : ℝ^n → ℝ^n` be
differentiable at every point of `Ω`. If, for every `x ∈ Ω`, every principal minor of `-J(x)`
(the determinant of the submatrix on rows and columns `I`, for every `I ⊆ {1, …, n}`) is
nonnegative, then any two nondegenerate zeros of `F` in `Ω` are equal.

Source: C. Soulé, ComPlexUs 1 (2003) 123–133, Theorem 1′. -/
theorem_wanted eq_of_principalMinors_nonneg (Ωi : Fin n → Set ℝ) (hopen : ∀ i, IsOpen (Ωi i))
    (hconn : ∀ i, (Ωi i).OrdConnected) {F : (Fin n → ℝ) → Fin n → ℝ}
    (hF : ∀ x ∈ Set.univ.pi Ωi, DifferentiableAt ℝ F x)
    (hminor : ∀ x ∈ Set.univ.pi Ωi, ∀ I : Finset (Fin n),
      0 ≤ ((-jacobian F x).submatrix (fun i : I => (i : Fin n))
        (fun i : I => (i : Fin n))).det)
    {a b : Fin n → ℝ} (ha : a ∈ Set.univ.pi Ωi) (hb : b ∈ Set.univ.pi Ωi)
    (ha0 : IsNondegenerateZero F a) (hb0 : IsNondegenerateZero F b) :
    a = b

end WantedExt.Biology.Biophysics.ThomasRuleWanted
