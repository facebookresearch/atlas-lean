/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kadison-Singer: unique extension of pure states (Oberwolfach Reports 17/2011)

Oberwolfach workshop Operator Algebras and Representation Theory: Frames, Wavelets and Fractals
(2011), introduction: does every pure state on the diagonal operators on `ℓ²` extend uniquely to a
state on `B(ℓ²)`? (Existence is clear; uniqueness is the Kadison-Singer problem.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

namespace MathlibExt.Analysis.KadisonSingerPureStateExtensionOWR4807Problem001Wanted

/-!
Source: workshop introduction, in Operator Algebras and Representation Theory: Frames, Wavelets and
Fractals, Oberwolfach Reports 8 (2011), no. 17, p. 902, DOI 10.4171/OWR/2011/17. UnsolvedMath record
UM-30001746 (`OWR-4807-001`), dataset ulamai/UnsolvedMath v1.8.0.

`H = ℓ²(ℕ)`. A state on `B(H)` is a linear functional `ψ` with `ψ 1 = 1` and `ψ(T* T) ≥ 0` (positive
functionals on a C*-algebra are automatically bounded). States and pure states on the diagonal
operators (the atomic masa `ℓ^∞`) are given by their values on diagonal operators; a pure state is
an extreme point of the diagonal states. A unique state extension is automatically pure. MathlibExt
proves the equivalent Anderson paving form (`kadison_singer_paving`); the reduction to pure states
is not in the repository.
-/

open scoped ComplexOrder

/-- The Hilbert space `ℓ²(ℕ)`. -/
abbrev Ell2 : Type := lp (fun _ : ℕ => ℂ) 2

/-- The `i`-th standard basis vector of `ℓ²(ℕ)`. -/
noncomputable def basisVec (i : ℕ) : Ell2 := lp.single 2 i 1

/-- `T` is a diagonal operator: `⟪e_i, T e_j⟫ = 0` for `i ≠ j`. The diagonal operators form the
atomic masa `ℓ^∞ ⊆ B(ℓ²)`. -/
def IsDiagonal (T : Ell2 →L[ℂ] Ell2) : Prop :=
  ∀ i j, i ≠ j → inner ℂ (basisVec i) (T (basisVec j)) = 0

/-- A state on `B(ℓ²)`: a linear functional `ψ` with `ψ 1 = 1` and `ψ (T* T) ≥ 0` for all `T`. -/
def IsState (ψ : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ) : Prop :=
  ψ 1 = 1 ∧ ∀ T, 0 ≤ ψ (star T * T)

/-- A state on the diagonal operators, given by its values on them: `φ` is additive and
`ℂ`-homogeneous on diagonal operators, `φ 1 = 1` and `φ (T* T) ≥ 0` for diagonal `T`. -/
def IsDiagonalState (φ : (Ell2 →L[ℂ] Ell2) → ℂ) : Prop :=
  (∀ S T, IsDiagonal S → IsDiagonal T → φ (S + T) = φ S + φ T) ∧
    (∀ (a : ℂ) T, IsDiagonal T → φ (a • T) = a * φ T) ∧ φ 1 = 1 ∧
    ∀ T, IsDiagonal T → 0 ≤ φ (star T * T)

/-- A pure state on the diagonal operators: an extreme point of the diagonal states, i.e. not a
proper convex combination of two diagonal states that differ from it on the diagonal operators. -/
def IsPureDiagonalState (φ : (Ell2 →L[ℂ] Ell2) → ℂ) : Prop :=
  IsDiagonalState φ ∧
    ∀ φ₁ φ₂ : (Ell2 →L[ℂ] Ell2) → ℂ, IsDiagonalState φ₁ → IsDiagonalState φ₂ →
      ∀ t : ℝ, 0 < t → t < 1 → (∀ T, IsDiagonal T → φ T = t * φ₁ T + (1 - t) * φ₂ T) →
        ∀ T, IsDiagonal T → φ₁ T = φ T

/-- The Kadison-Singer problem (Oberwolfach Report 17/2011, p. 902): every pure state on the
diagonal operators of `B(ℓ²)` extends to a unique state on `B(ℓ²)`. -/
def pureStateUniqueExtension : Prop :=
  ∀ φ : (Ell2 →L[ℂ] Ell2) → ℂ, IsPureDiagonalState φ →
    ∃ ψ : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ, IsState ψ ∧ (∀ T, IsDiagonal T → ψ T = φ T) ∧
      ∀ ψ' : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ, IsState ψ' → (∀ T, IsDiagonal T → ψ' T = φ T) → ψ' = ψ

/--
Resolved true: Marcus, Spielman and Srivastava proved Weaver's `KS₂` conjecture and Anderson's
paving conjecture, each known to imply that every pure state on the diagonal operators of `B(ℓ²)`
has a unique extension to a state on `B(ℓ²)` (Kadison-Singer). Source: workshop introduction, in
Operator Algebras and Representation Theory: Frames, Wavelets and Fractals, Oberwolfach Reports 8
(2011), no. 17, p. 902, DOI 10.4171/OWR/2011/17; resolution: A. W. Marcus, D. A. Spielman and N.
Srivastava, Interlacing families II: Mixed characteristic polynomials and the Kadison-Singer
problem, Ann. of Math. (2) 182 (2015), 327-350, proof of Weaver's KS2 conjecture and of Anderson's
paving conjecture, each known to imply that every pure state on the diagonal masa of B(ℓ²) has a
unique state extension, https://doi.org/10.4007/annals.2015.182.1.8.
-/
public theorem_wanted pureStateUniqueExtension_holds : pureStateUniqueExtension

end MathlibExt.Analysis.KadisonSingerPureStateExtensionOWR4807Problem001Wanted
