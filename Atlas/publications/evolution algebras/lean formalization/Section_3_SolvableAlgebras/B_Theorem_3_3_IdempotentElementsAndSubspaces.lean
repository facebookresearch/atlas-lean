/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Section_1_Introduction.A_EvolutionAlgebra
import Appendix_FixedPoint.A_FixedPoint
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.Group.Idempotent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Theorem 3.3: nonzero idempotents versus idempotent subspaces

Paper Theorem 3.3 (`idempotentiff`): over an algebraically closed field,
`E` admits a nonzero idempotent element ↔ `E` admits a nontrivial
idempotent subspace `V` with `N(V) = {0}`.

Reading of "N(V) = 0": the zero SET `{0}`. (`0 ∈ N(V)` always since
`0 * 0 = 0`, so the paper's "= 0" can only mean triviality.)

Proved via `EvolutionAlgebras.fixedPoint_of_idempotent` (the projective
fixed-point principle, in `A_FixedPoint` — the largest part of the
formalization).
Finite-dimensionality enters as `[FiniteDimensional K E]` (which is
`Module.Finite` by definition); the fixed-point principle itself takes it as
an explicit `Module.Finite` hypothesis.

## Main results

* `EvolutionAlgebras.IdempotentIff.forward`: a nonzero idempotent spans
  an idempotent subspace with `N(V) = {0}`.
* `EvolutionAlgebras.IdempotentIff.backward`: an idempotent subspace
  with `N(V) = {0}` yields a nonzero idempotent (via the fixed-point
  principle).
* `EvolutionAlgebras.IdempotentIff.idempotent_iff`: the equivalence.
-/

namespace EvolutionAlgebras
namespace IdempotentIff

variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
  [NonUnitalNonAssocAlgebra K E]

/-- **Helper.** Scalar action through a square: `(a • y) * (b • y) = (a * b) • (y * y)`.
Used for the rescaling computations in `forward` and `backward` below. -/
theorem smul_mul_smul (a b : K) (y : E) :
    (a • y) * (b • y) = (a * b) • (y * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_smul]

/- The projective fixed-point principle used by `backward` below is
`EvolutionAlgebras.fixedPoint_of_idempotent` from `A_FixedPoint.lean` (see
`evolution_algebras_comparator.json`). It is stated with minimal hypotheses so that it
applies here directly. -/

/-- **Paper Theorem 3.3.** Forward direction of paper Theorem `idempotentiff`: a nonzero idempotent
spans an idempotent subspace with `N(V) = {0}`. Stated for a finite-dimensional
evolution algebra, as in the paper (the computation itself needs less). -/
theorem forward {x : E} [EvolutionAlgebra K E] [FiniteDimensional K E]
    (hx : IsIdempotentElem x) (hne : x ≠ 0) :
    ∃ V : Submodule K E, V ≠ ⊥ ∧ IsIdempotentSubmodule K E V ∧
      absNilpotent K E V = {0} := by
  have hx_eq : x * x = x := hx
  refine ⟨Submodule.span K {x}, ?_, ?_, ?_⟩
  · -- Nontrivial: `x ∈ span{x}`, and `x ≠ 0`.
    intro hbot
    apply hne
    have hmem : x ∈ Submodule.span K ({x} : Set E) :=
      Submodule.subset_span (Set.mem_singleton x)
    rw [hbot] at hmem
    rw [Submodule.mem_bot] at hmem
    exact hmem
  · -- Idempotent: `(span{x})² = span{x}`.
    unfold IsIdempotentSubmodule
    apply le_antisymm
    · unfold square
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      obtain ⟨p, hp⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hb
      subst hp
      subst hq
      rw [smul_mul_smul, hx_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
    · rw [Submodule.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      unfold square
      apply Submodule.subset_span
      refine ⟨x, ?_, x, ?_, hx_eq⟩
      · exact Submodule.subset_span (Set.mem_singleton x)
      · exact Submodule.subset_span (Set.mem_singleton x)
  · -- `N(span{x}) = {0}`.
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · simp only [absNilpotent, Set.mem_ofPred_eq]
      refine ⟨Submodule.zero_mem _, ?_⟩
      change (0 : E) * (0 : E) = (0 : E)
      exact mul_zero _
    · intro y hy
      simp only [absNilpotent, Set.mem_ofPred_eq] at hy
      obtain ⟨hmem, habs⟩ := hy
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      subst ha
      have habs0 : (a • x) * (a • x) = 0 := habs
      rw [smul_mul_smul, hx_eq] at habs0
      -- `(a * a) • x = 0` with `x ≠ 0` forces `a * a = 0` (`a * a` is a unit otherwise).
      have ha0 : a * a = 0 := by
        by_contra hne0
        have h1 : x = ((a * a)⁻¹ * (a * a)) • x := by
          rw [inv_mul_cancel₀ hne0, one_smul]
        rw [← smul_smul, habs0, smul_zero] at h1
        exact hne h1
      have haz : a = 0 := mul_self_eq_zero.mp ha0
      rw [haz, zero_smul]

/-- Backward direction of paper Theorem `idempotentiff`: an idempotent
subspace with `N(V) = {0}` yields a nonzero idempotent, via
`EvolutionAlgebras.fixedPoint_of_idempotent` (rescaling the fixed point by
`lam⁻¹`). -/
theorem backward (V : Submodule K E) [IsAlgClosed K] [EvolutionAlgebra K E]
    [FiniteDimensional K E] (hneV : V ≠ ⊥)
    (hV : IsIdempotentSubmodule K E V) (hN : absNilpotent K E V = {0}) :
    ∃ e : E, IsIdempotentElem e ∧ e ≠ 0 := by
  obtain ⟨x, -, hx0, lam, hlam0, hlam⟩ :=
    fixedPoint_of_idempotent K E V inferInstance hV hN hneV
  have hinv : lam⁻¹ * lam⁻¹ * lam = lam⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
  refine ⟨lam⁻¹ • x, ?_, ?_⟩
  · change (lam⁻¹ • x) * (lam⁻¹ • x) = lam⁻¹ • x
    rw [smul_mul_smul, hlam, smul_smul, hinv]
  · intro hz
    apply hx0
    have h2 : lam • (lam⁻¹ • x) = (0 : E) := by rw [hz, smul_zero]
    rw [smul_smul, mul_inv_cancel₀ hlam0, one_smul] at h2
    exact h2

/-- Paper Theorem 3.3 (`idempotentiff`): nonzero idempotent elements
correspond to nontrivial idempotent subspaces with `N(V) = {0}`. Combines
`forward` and `backward`; the backward direction uses
`EvolutionAlgebras.fixedPoint_of_idempotent` (the projective fixed-point
principle, in `A_FixedPoint`). -/
theorem idempotent_iff [IsAlgClosed K] [EvolutionAlgebra K E]
    [FiniteDimensional K E] :
    (∃ x : E, IsIdempotentElem x ∧ x ≠ 0) ↔
      ∃ V : Submodule K E, V ≠ ⊥ ∧ IsIdempotentSubmodule K E V ∧
        absNilpotent K E V = {0} := by
  constructor
  · rintro ⟨x, hx, hne⟩
    obtain ⟨V, h1, h2, h3⟩ := forward K E hx hne
    exact ⟨V, h1, h2, h3⟩
  · rintro ⟨V, hneV, hV, hN⟩
    exact backward K E V hneV hV hN

end IdempotentIff
end EvolutionAlgebras
