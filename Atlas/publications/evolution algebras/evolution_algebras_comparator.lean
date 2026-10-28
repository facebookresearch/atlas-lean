/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Section_1_Introduction.A_EvolutionAlgebra
import Section_1_Introduction.B_Conjecture_1_1_SolvableIffIdempotentFree
import Section_2_Preliminaries.A_Preliminaries

/-!
# Challenge

Statements for `lake comparator --config evolution_algebras_comparator.json`.
-/

namespace EvolutionAlgebras

/-- Conjecture 1.1, refuted by Example 2.1. -/
theorem conjecture_false : ¬ Conjecture := by
  sorry

/-- Lemma 3.1. -/
theorem einfty_is_idempotent
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    square K E (derivedSeriesInf K E) = derivedSeriesInf K E ∧
      ∀ V : Submodule K E, square K E V = V → V ≤ derivedSeriesInf K E := by
  sorry

/-- Theorem 3.2, conditions (1) ↔ (3). -/
theorem solvable_iff_no_idempotent_subspace
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsSolvable K E ↔
      ∀ V : Submodule K E, IsIdempotentSubmodule K E V → V = ⊥ := by
  sorry

/-- Theorem 3.2, conditions (1) ↔ (2). -/
theorem solvable_iff_derivedSeriesInf_eq_bot
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsSolvable K E ↔ derivedSeriesInf K E = ⊥ := by
  sorry

namespace IdempotentIff

/-- Theorem 3.3. -/
theorem idempotent_iff
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [IsAlgClosed K] [EvolutionAlgebra K E]
    [FiniteDimensional K E] :
    (∃ x : E, IsIdempotentElem x ∧ x ≠ 0) ↔
      ∃ V : Submodule K E, V ≠ ⊥ ∧ IsIdempotentSubmodule K E V ∧
        absNilpotent K E V = {0} := by
  sorry

end IdempotentIff

namespace SolvableCorollary

/-- Corollary 3.4. -/
theorem isSolvable_iff_no_nonzero_idempotent (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E]
    [IsAlgClosed K] [FiniteDimensional K E]
    (hN : absNilpotent K E (derivedSeriesInf K E) = {0}) :
    IsSolvable K E ↔ ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0 := by
  sorry

end SolvableCorollary

/- The following algebra structure on `𝓔^(∞)` is needed to state Remark 3.6. -/
instance einfMul (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    Mul ↥(derivedSeriesInf K E) where
  mul x y :=
    ⟨x.1 * y.1, by
      have hmem : x.1 * y.1 ∈ square K E (derivedSeriesInf K E) :=
        Submodule.subset_span ⟨x.1, x.2, y.1, y.2, rfl⟩
      rwa [(einfty_is_idempotent K E).1] at hmem⟩

theorem einf_coe_mul (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E]
    (x y : ↥(derivedSeriesInf K E)) :
    ((x * y : ↥(derivedSeriesInf K E)) : E) = x.1 * y.1 :=
  rfl

instance einfSemiring (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    NonUnitalNonAssocSemiring ↥(derivedSeriesInf K E) where
  toAddCommMonoid := inferInstance
  toMul := inferInstance
  left_distrib := by
    intro a b c
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_add, mul_add]
  right_distrib := by
    intro a b c
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_add, add_mul]
  zero_mul := by
    intro a
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_zero, zero_mul]
  mul_zero := by
    intro a
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_zero, mul_zero]

instance einfTower (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsScalarTower K ↥(derivedSeriesInf K E) ↥(derivedSeriesInf K E) :=
  ⟨fun x y z => Subtype.ext (smul_assoc x y.1 z.1)⟩

instance einfComm (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    SMulCommClass K ↥(derivedSeriesInf K E) ↥(derivedSeriesInf K E) :=
  ⟨fun x y z => Subtype.ext (smul_comm x y.1 z.1)⟩

instance einfAlgebra (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    NonUnitalNonAssocAlgebra K ↥(derivedSeriesInf K E) where
  toModule := inferInstance
  toIsScalarTower := inferInstance
  toSMulCommClass := inferInstance

/-- Remark 3.6. -/
theorem einfty_absNilpotent_eq_zero
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E]
    [EvolutionAlgebra K ↥(derivedSeriesInf K E)] :
    absNilpotent K E (derivedSeriesInf K E) = {0} := by
  sorry

/-- Appendix. -/
theorem fixedPoint_of_idempotent
    (K E : Type*) [Field K] [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) [IsAlgClosed K]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  sorry

end EvolutionAlgebras
