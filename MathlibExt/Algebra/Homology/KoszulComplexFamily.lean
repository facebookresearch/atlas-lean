/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.KoszulComplexAugmentation
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Koszul complexes of finite families

A finite family `a : I → R` defines a coefficient functional on the standard
free module `I → R`, hence a Koszul complex. Its range ideal is the ideal
spanned by the family. The complex is supported through degree
`Fintype.card I`, and every term is finite free and projective.

## Main declarations

* `KoszulComplex.familyFunctional`
* `KoszulComplex.familyIdeal_eq_span`
* `KoszulComplex.familyComplex`
* `KoszulComplex.familyComplex_isZero_above`
* `KoszulComplex.familyComplex_projective`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R]
variable {I : Type v} [Fintype I]

/-- The coefficient functional associated to a finite family. -/
def familyFunctional (a : I → R) : (I → R) →ₗ[R] R :=
  Fintype.linearCombination R a

/-- The family functional sends a standard basis vector to its coefficient. -/
theorem familyFunctional_single [DecidableEq I] (a : I → R) (i : I) :
    familyFunctional R a (Pi.single i 1) = a i := by
  classical
  simp [familyFunctional]

/-- On an ordered wedge of standard basis vectors, the finite-family Koszul
differential has the usual signed deletion formula. -/
theorem familyDifferential_apply_basis [DecidableEq I]
    (a : I → R) (n : ℕ) (b : Fin (n + 1) → I) :
    differential R (I → R) (familyFunctional R a) n
        (exteriorPower.ιMulti R (n + 1)
          (fun j ↦ (Pi.single (b j) 1 : I → R))) =
      ∑ j : Fin (n + 1),
        (((-1 : R) ^ j.val) * a (b j)) •
          exteriorPower.ιMulti R n
            (fun q ↦ (Pi.single (b (j.succAbove q)) 1 : I → R)) := by
  rw [differential_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro j _
  rw [familyFunctional_single]
  simp only [smul_smul]
  rfl

/-- The quotient augmentation of a finite-family Koszul complex sends the
scalar multiple of the degree-zero generator to the corresponding quotient
class. -/
theorem familyAugmentationLinear_apply_smul_ιMulti
    (a : I → R) (r : R) (b : Fin 0 → (I → R)) :
    augmentationLinear R (I → R) (familyFunctional R a)
        (r • exteriorPower.ιMulti R 0 b) =
      Ideal.Quotient.mk
        (ideal R (I → R) (familyFunctional R a)) r := by
  rw [map_smul, augmentationLinear_apply_ιMulti, map_one]
  exact (Algebra.algebraMap_eq_smul_one r).symm

/-- The range ideal of the family functional is the ideal spanned by the family. -/
theorem familyIdeal_eq_span (a : I → R) :
    ideal R (I → R) (familyFunctional R a) = Ideal.span (Set.range a) := by
  change LinearMap.range (Fintype.linearCombination R a) = _
  rw [Fintype.range_linearCombination, Ideal.submodule_span_eq]

/-- The Koszul complex of a finite family. -/
def familyComplex (a : I → R) :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  complex R (I → R) (familyFunctional R a)

/-- A finite-family Koszul complex vanishes strictly above the family's cardinality. -/
theorem familyComplex_isZero_above (a : I → R) (n : ℕ)
    (hn : Fintype.card I < n) :
    IsZero ((familyComplex R a).X n) := by
  rw [familyComplex, complex_X]
  classical
  let b : Module.Basis I R (I → R) := Pi.basisFun R I
  let _ : Subsingleton (⋀[R]^n (I → R)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (R := R) (g := b) b.span_eq n (by simpa using hn)
  exact ModuleCat.isZero_of_subsingleton _

/-- Every term of a finite-family Koszul complex is projective. -/
theorem familyComplex_projective (a : I → R) (n : ℕ) :
    Projective ((familyComplex R a).X n) := by
  rw [familyComplex, complex_X]
  classical
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact ModuleCat.projective_of_free ((Pi.basisFun R I).exteriorPower n)

/-- Every term of a finite-family Koszul complex is free. -/
theorem familyComplex_free (a : I → R) (n : ℕ) :
    Module.Free R ((familyComplex R a).X n) := by
  rw [familyComplex, complex_X]
  infer_instance

/-- Every term of a finite-family Koszul complex is finitely generated. -/
theorem familyComplex_finite (a : I → R) (n : ℕ) :
    Module.Finite R ((familyComplex R a).X n) := by
  rw [familyComplex, complex_X]
  infer_instance

end KoszulComplex
