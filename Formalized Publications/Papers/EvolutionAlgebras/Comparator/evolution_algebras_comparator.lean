/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Comparator challenge: evolution algebras

Challenge module for the comparator (see
`evolution_algebras_comparator.json`). The definitions below are stated
independently in this file, by design: they must NOT be imported from
the solution (`Formalization/`), otherwise changing a solution
definition would change both sides of the comparison and the
comparator would certify nothing about the definitions themselves.
They duplicate the paper-facing definitions of the solution under the
same names, and every one of them is enumerated in `definition_names`
in the JSON config. The theorems are the paper-facing results, stated
with these challenge definitions and proved with `sorry` here; the
comparator checks that the solution proves the same statements (and
uses the same definitions) with only the permitted axioms.
-/

universe u v

/-- Challenge copy of the solution's `NonUnitalNonAssocAlgebra`. -/
class NonUnitalNonAssocAlgebra (R A : Type*) [CommSemiring R]
    [NonUnitalNonAssocSemiring A]
  extends Module R A, IsScalarTower R A A, SMulCommClass R A A

/-- Challenge copy of the solution's `EvolutionAlgebra`. -/
class EvolutionAlgebra (K : Type u) (E : Type v) [Field K] [NonUnitalNonAssocSemiring E]
    [NonUnitalNonAssocAlgebra K E] : Prop where
  exists_natural_basis : ∃ (n : ℕ) (b : Module.Basis (Fin n) K E),
    ∀ i j : Fin n, i ≠ j → b i * b j = 0

namespace EvolutionAlgebra

variable (K : Type u) (E : Type v) [Field K] [NonUnitalNonAssocSemiring E]
  [NonUnitalNonAssocAlgebra K E]

/-- Challenge copy of `EvolutionAlgebra.natural_basis`. -/
noncomputable def natural_basis [self : EvolutionAlgebra K E] :
    Σ' (n : ℕ), Module.Basis (Fin n) K E :=
  have h := Classical.indefiniteDescription _ self.exists_natural_basis
  ⟨h.val, Classical.indefiniteDescription _ h.property |>.val⟩

/-- Challenge copy of `EvolutionAlgebra.struct_matrix`. -/
noncomputable def struct_matrix (n : ℕ) (b : Module.Basis (Fin n) K E) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => b.repr (b i * b i) j

end EvolutionAlgebra

namespace EvolutionAlgebras

section ChallengeDefinitions

variable (K E : Type*) [CommSemiring K] [NonUnitalNonAssocSemiring E] [Module K E]

/-- Challenge copy of `EvolutionAlgebras.square`. -/
def square (V : Submodule K E) : Submodule K E :=
  Submodule.span K {z | ∃ x ∈ V, ∃ y ∈ V, x * y = z}

/-- Challenge copy of `EvolutionAlgebras.IsIdempotentSubmodule`. -/
def IsIdempotentSubmodule (V : Submodule K E) : Prop :=
  square K E V = V

/-- Challenge copy of `EvolutionAlgebras.derivedSeriesOfSubmodule`. -/
def derivedSeriesOfSubmodule (k : ℕ) : Submodule K E → Submodule K E :=
  (fun V => square K E V)^[k]

/-- Challenge copy of `EvolutionAlgebras.derivedSeries`. -/
abbrev derivedSeries (k : ℕ) : Submodule K E :=
  derivedSeriesOfSubmodule K E k ⊤

/-- Challenge copy of `EvolutionAlgebras.derivedSeriesInf`. -/
def derivedSeriesInf : Submodule K E :=
  ⨅ k, derivedSeries K E k

/-- Challenge copy of `EvolutionAlgebras.IsSolvable`. -/
class IsSolvable : Prop where
  mk_int ::
  solvable_int : ∃ k, derivedSeries K E k = ⊥

/-- Challenge copy of `EvolutionAlgebras.IsAbsNilpotent`. -/
def IsAbsNilpotent (x : E) : Prop :=
  x * x = 0

/-- Challenge copy of `EvolutionAlgebras.absNilpotent`. -/
def absNilpotent (V : Submodule K E) : Set E :=
  {x | x ∈ V ∧ IsAbsNilpotent E x}

/-- Challenge copy of `EvolutionAlgebras.Conjecture` (Paper Conjecture 1.1). -/
def Conjecture : Prop :=
  ∀ (E : Type 0) [NonUnitalNonAssocSemiring E]
    [NonUnitalNonAssocAlgebra ℂ E] [EvolutionAlgebra ℂ E],
    IsSolvable ℂ E ↔ ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0

end ChallengeDefinitions
theorem conjecture_false : ¬ Conjecture := by
  sorry

theorem einfty_is_idempotent
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    square K E (derivedSeriesInf K E) = derivedSeriesInf K E ∧
      ∀ V : Submodule K E, square K E V = V → V ≤ derivedSeriesInf K E := by
  sorry

theorem solvable_iff_no_idempotent_subspace
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsSolvable K E ↔
      ∀ V : Submodule K E, IsIdempotentSubmodule K E V → V = ⊥ := by
  sorry

theorem solvable_iff_derivedSeriesInf_eq_bot
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsSolvable K E ↔ derivedSeriesInf K E = ⊥ := by
  sorry

namespace IdempotentIff

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

theorem isSolvable_iff_no_nonzero_idempotent (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E]
    [IsAlgClosed K] [FiniteDimensional K E]
    (hN : absNilpotent K E (derivedSeriesInf K E) = {0}) :
    IsSolvable K E ↔ ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0 := by
  sorry

end SolvableCorollary

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

theorem einfty_absNilpotent_eq_zero
    (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E]
    [EvolutionAlgebra K ↥(derivedSeriesInf K E)] :
    absNilpotent K E (derivedSeriesInf K E) = {0} := by
  sorry

theorem fixedPoint_of_idempotent
    (K E : Type*) [Field K] [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) [IsAlgClosed K]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  sorry

end EvolutionAlgebras
