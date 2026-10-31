/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Section_1_Introduction.A_EvolutionAlgebra
import Appendix_FixedPoint.A_FixedPoint
import Section_2_Preliminaries.A_Preliminaries
import Section_3_SolvableAlgebras.A_Lemma_3_1_Theorem_3_2_SolvableIff
import Mathlib.Algebra.Group.Idempotent
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Corollary 3.4: the conditional conjecture

Paper Corollary 3.4: under `N(𝓔^(∞)) = 0`, the original
García-Martínez / Pérez-Rodríguez conjecture holds — solvability is
equivalent to having no nonzero idempotent elements.

The forward direction (solvable → no idempotents) is general: an idempotent
lies in every derived-series term, hence in `⊥`
(`no_nonzero_idempotent_of_isSolvable`).

The converse goes through the two main theorems: non-solvability leaves the
stabilized term `𝓔^(∞)` nontrivial and idempotent (paper Lemma `einftyisidempotent`,
Lean `einfty_is_idempotent`), and since `N(𝓔^(∞)) = 0`, the fixed-point principle
(`fixedPoint_of_idempotent`, paper Theorem `idempotentiff` backward direction)
produces a nonzero idempotent (`isSolvable_of_no_nonzero_idempotent`). Both halves
combine into `isSolvable_iff_no_nonzero_idempotent`.

Hypothesis note: the statements match the paper (finite-dimensional
evolution algebra over an algebraically closed field); the module structure
and scalar compatibility come from the algebra structure. The fixed-point
principle is applied from `A_FixedPoint`, whose minimal hypotheses are
satisfied here directly.

## Main results

* `EvolutionAlgebras.SolvableCorollary.no_nonzero_idempotent_of_isSolvable`:
  a solvable algebra admits no nonzero idempotents (paper Corollary 3.4, forward).
* `EvolutionAlgebras.SolvableCorollary.isSolvable_of_no_nonzero_idempotent`:
  under `N(𝓔^(∞)) = 0`, lack of idempotents forces solvability (converse).
* `EvolutionAlgebras.SolvableCorollary.isSolvable_iff_no_nonzero_idempotent`:
  the full equivalence (paper Corollary 3.4).
-/

namespace EvolutionAlgebras
namespace SolvableCorollary

/-- **Paper Corollary 3.4.** A solvable algebra admits no nonzero idempotent elements: an
idempotent lies in every derived-series term, hence in `⊥`.
Paper Corollary 3.4, forward direction, stated for the paper's field context
(the argument itself needs only a commutative semiring). -/
theorem no_nonzero_idempotent_of_isSolvable (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E]
    (hsol : IsSolvable K E) :
    ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0 := by
  rintro ⟨x, hx, hne⟩
  obtain ⟨k, hk⟩ := hsol.solvable
  have hxmem : x ∈ derivedSeries K E k :=
    idempotent_mem_derivedSeries K E hx k
  rw [hk, Submodule.mem_bot] at hxmem
  exact hne hxmem

/-- **Helper.** Scalar action through a square: `(a • y) * (b • y) = (a * b) • (y * y)`.
The analogue of `IdempotentIff.smul_mul_smul` for this file's hypotheses
(the scalar-compatibility laws are explicit hypotheses here). Used for the
rescaling computation in `isSolvable_of_no_nonzero_idempotent`. -/
theorem smul_mul_smul (K E : Type*) [CommSemiring K] [NonUnitalNonAssocSemiring E]
    [Module K E] [IsScalarTower K E E] [SMulCommClass K E E] (a b : K) (y : E) :
    (a • y) * (b • y) = (a * b) • (y * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_smul]

/-- Converse direction of paper Corollary 3.4: if `N(𝓔^(∞)) = 0`
    (stated as `N`
of `derivedSeriesInf`, which equals the paper's stabilized value by
`derivedSeriesInf_eq_of_stabilizes`) and `E` has no nonzero idempotents, then
`E` is solvable.

Prerequisites: `derivedSeries_stabilizes` and `derivedSeriesInf_eq_of_stabilizes`
(so `𝓔^(∞)` is a concrete stable term), `einfty_is_idempotent` (paper Lemma
`einftyisidempotent`: `𝓔^(∞)` is idempotent, hence the witness subspace), and
`fixedPoint_of_idempotent` (paper Theorem `idempotentiff`, backward direction:
the fixed point rescales to a nonzero idempotent).

`FiniteDimensional` feeds `einfty_is_idempotent` and the fixed-point
principle (which takes it as an explicit `Module.Finite` hypothesis). -/
theorem isSolvable_of_no_nonzero_idempotent (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E]
    [IsAlgClosed K] [FiniteDimensional K E]
    (hN : absNilpotent K E (derivedSeriesInf K E) = {0})
    (hno : ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0) : IsSolvable K E := by
  classical
  -- Assume non-solvability; the stabilized term will yield an idempotent.
  by_contra hns
  -- `𝓔^(∞)` is idempotent (Lemma `einfty_is_idempotent`) and nontrivial:
  -- were it `⊥`, a stable derived term would be `⊥`, making `E` solvable.
  have hidem : square K E (derivedSeriesInf K E) = derivedSeriesInf K E :=
    (einfty_is_idempotent K E).1
  have hVne : derivedSeriesInf K E ≠ ⊥ := by
    intro hbot
    obtain ⟨l, hl⟩ := derivedSeries_stabilizes K E
    have hinf : derivedSeriesInf K E = derivedSeries K E l :=
      derivedSeriesInf_eq_of_stabilizes K E hl
    exact hns (IsSolvable.mk K E (by rw [← hinf]; exact hbot))
  -- The fixed-point principle gives `x * x = lam • x` with `lam ≠ 0`;
  -- rescaling by `lam⁻¹` (the `backward` computation of paper Theorem
  -- `idempotentiff`) produces a nonzero idempotent, contradicting `hno`.
  obtain ⟨x, -, hx0, lam, hlam0, hlam⟩ :=
    fixedPoint_of_idempotent K E (derivedSeriesInf K E) inferInstance hidem hN hVne
  have hinv : lam⁻¹ * lam⁻¹ * lam = lam⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
  apply hno
  refine ⟨lam⁻¹ • x, ?_, ?_⟩
  · change (lam⁻¹ • x) * (lam⁻¹ • x) = lam⁻¹ • x
    rw [smul_mul_smul K E, hlam, smul_smul, hinv]
  · intro hz
    apply hx0
    have h2 : lam • (lam⁻¹ • x) = (0 : E) := by rw [hz, smul_zero]
    rw [smul_smul, mul_inv_cancel₀ hlam0, one_smul] at h2
    exact h2

/-- Paper Corollary 3.4 in full: under `N(𝓔^(∞)) = 0`, solvability is
    equivalent
to having no nonzero idempotent elements. Combines
`no_nonzero_idempotent_of_isSolvable` (forward) with
`isSolvable_of_no_nonzero_idempotent` (converse). -/
theorem isSolvable_iff_no_nonzero_idempotent (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E]
    [IsAlgClosed K] [FiniteDimensional K E]
    (hN : absNilpotent K E (derivedSeriesInf K E) = {0}) :
    IsSolvable K E ↔ ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0 :=
  ⟨fun hsol => no_nonzero_idempotent_of_isSolvable K E hsol,
    fun hno => isSolvable_of_no_nonzero_idempotent K E hN hno⟩

end SolvableCorollary
end EvolutionAlgebras
