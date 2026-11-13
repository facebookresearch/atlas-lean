/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A non-diagonalizable pure state on B(ℓ²) exists in ZFC (AimPL Set theory and C* algebras, 5.3)

AimPL, Set theory and C* algebras, Problem 5.3: consider the statement 'every pure state on `B(H)`
is diagonalizable'. Is it consistent with ZFC? (Its negation follows from the Continuum Hypothesis
(Akemann-Weaver) or even from Martin's Axiom (Farah-Weaver).)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import WantedExt.Analysis.KadisonSingerPureStateExtensionOWR4807Problem001Wanted

@[expose] public section

namespace MathlibExt.Analysis.NonDiagonalizablePureStateAIMFunctionalAnalysisProblem33Wanted

/-!
Source: AimPL: Set theory and C* algebras, Problem 5.3, http://aimpl.org/settheorycstar/5/.
UnsolvedMath record UM-20001474 (`AIM-FUNCTIONAL_ANALYSIS-0033`), dataset ulamai/UnsolvedMath
v1.8.0.

`H = ℓ²(ℕ)`. A state is a linear functional `ψ` on `B(ℓ²)` with `ψ 1 = 1` and `ψ (T* T) ≥ 0`
(`Ell2` and `IsState` of the Kadison-Singer entry, Oberwolfach Reports 17/2011); a pure state is a
state that is not a proper convex combination of two other states. Following Koszmider,
`φ` is diagonalizable when `φ(T) = lim_{k → U} ⟨T eₖ, eₖ⟩` for an orthonormal basis `(eₖ)` of `ℓ²`
and an ultrafilter `U` on `ℕ`. The statement whose consistency is asked is the target; a ZFC proof
of its negation answers the question negatively.
-/

open MathlibExt.Analysis.KadisonSingerPureStateExtensionOWR4807Problem001Wanted (Ell2 IsState)

/-- A pure state on `B(ℓ²)`: a state that is not a proper convex combination of two other states. -/
def IsPureState (φ : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ) : Prop :=
  IsState φ ∧ ∀ ψ₁ ψ₂ : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ, IsState ψ₁ → IsState ψ₂ →
    ∀ t : ℝ, 0 < t → t < 1 → φ = (t : ℂ) • ψ₁ + ((1 - t : ℝ) : ℂ) • ψ₂ → ψ₁ = φ

/-- A state `φ` on `B(ℓ²)` is diagonalizable: `φ(T) = lim_{k → U} ⟨T eₖ, eₖ⟩` for some orthonormal
basis `(eₖ)` of `ℓ²` and some ultrafilter `U` on `ℕ` (Mathlib's inner product is conjugate-linear
in the first argument, so `⟨T eₖ, eₖ⟩` is `inner ℂ (e k) (T (e k))`). -/
def IsDiagonalizable (φ : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ) : Prop :=
  ∃ (e : HilbertBasis ℕ ℂ Ell2) (U : Ultrafilter ℕ), ∀ T : Ell2 →L[ℂ] Ell2,
    Filter.Tendsto (fun k => inner ℂ (e k) (T (e k))) (U : Filter ℕ) (nhds (φ T))

/-- Anderson's conjecture, the statement whose consistency with ZFC AimPL Problem 5.3 (Set theory
and C* algebras) asks about: every pure state on `B(ℓ²)` is diagonalizable. -/
def everyPureStateDiagonalizable : Prop :=
  ∀ φ : (Ell2 →L[ℂ] Ell2) →ₗ[ℂ] ℂ, IsPureState φ → IsDiagonalizable φ

/--
Resolved false in ZFC, so the statement is not consistent: Koszmider constructed, without extra
set-theoretic axioms, a pure state on `B(ℓ²)` that is not of the form `T ↦ lim_{k → u} ⟨T eₖ, eₖ⟩`
for any orthonormal basis `(eₖ)` and ultrafilter `u` on `ℕ` (Theorem 11), a counterexample to
Anderson's conjecture. Source: AimPL: Set theory and C* algebras, Problem 5.3,
http://aimpl.org/settheorycstar/5/; resolution: P. Koszmider, A non-diagonalizable pure state, Proc.
Natl. Acad. Sci. USA 117 (2020), 33084-33089, Theorem 11 (a ZFC construction): there is a
non-diagonalizable pure state on B(ℓ²), i.e. one not of the form lim_u ⟨T(e_k), e_k⟩ for any
orthonormal basis (e_k) of ℓ² and ultrafilter u on ℕ; a counterexample to Anderson's conjecture,
https://doi.org/10.1073/pnas.2011885117.
-/
public theorem_wanted everyPureStateDiagonalizable_refuted : ¬ everyPureStateDiagonalizable

end MathlibExt.Analysis.NonDiagonalizablePureStateAIMFunctionalAnalysisProblem33Wanted
