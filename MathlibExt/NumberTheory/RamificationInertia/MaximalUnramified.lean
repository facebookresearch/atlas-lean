/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.Algebra.RestrictScalars

/-! Finite formally unramified intermediate fields relative to a base ring, their
supremum, its universal property, and automorphism invariance. -/
@[expose] public section

namespace IntermediateField

variable {A K L : Type*} [CommRing A] [Field K] [Field L]
variable [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- **Finite unramified intermediate fields.** Let $A$ be a commutative ring and $L/K$ a field
extension such that the map $A \to L$ factors as $A \to K \to L$. An intermediate field $E$ of
$L/K$ is finite unramified relative to $A$ if $E$ is finite-dimensional over $K$ and the
integral closure of $A$ in $E$ is formally unramified over $A$. -/
def IsFiniteUnramified (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (E : IntermediateField K L) : Prop :=
  FiniteDimensional K E ∧ Algebra.FormallyUnramified A (integralClosure A E)

/-- **Maximal unramified subextension.** Let $A$ be a commutative ring and $L/K$ a field
extension such that the map $A \to L$ factors as $A \to K \to L$. The maximal unramified
subextension of $L/K$ relative to $A$ is the supremum, in the lattice of intermediate fields of
$L/K$, of all intermediate fields of $L/K$ that are finite unramified relative to $A$.

The supremum need not itself be finite or formally unramified. -/
noncomputable def maximalUnramifiedSubextension (A K L : Type*) [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] : IntermediateField K L :=
  ⨆ (E : IntermediateField K L) (_ : IsFiniteUnramified A E), E

/-- **Finite unramified subfields lie in the maximal unramified subextension.** Let $A$ be a
commutative ring and $L/K$ a field extension such that the map $A \to L$ factors as
$A \to K \to L$. Every intermediate field $E$ of $L/K$ that is finite unramified relative to $A$
is contained in the maximal unramified subextension of $L/K$ relative to $A$. -/
theorem le_maximalUnramifiedSubextension {E : IntermediateField K L}
    (hE : IsFiniteUnramified A E) :
    E ≤ maximalUnramifiedSubextension A K L :=
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

/-- **Universal property of the maximal unramified subextension.** Let $A$ be a commutative ring
and $L/K$ a field extension such that the map $A \to L$ factors as $A \to K \to L$. An
intermediate field $F$ of $L/K$ contains the maximal unramified subextension of $L/K$ relative
to $A$ if and only if $F$ contains every intermediate field of $L/K$ that is finite unramified
relative to $A$. -/
@[simp]
theorem maximalUnramifiedSubextension_le_iff {F : IntermediateField K L} :
    maximalUnramifiedSubextension A K L ≤ F ↔
      ∀ E : IntermediateField K L, IsFiniteUnramified A E → E ≤ F := by
  constructor
  · intro h E hE
    exact (le_maximalUnramifiedSubextension hE).trans h
  · intro h
    unfold maximalUnramifiedSubextension
    apply iSup_le
    intro E
    apply iSup_le
    intro hE
    exact h E hE

/-- **Automorphisms preserve finite unramified subfields.** Let $A$ be a commutative ring and
$L/K$ a field extension such that the map $A \to L$ factors as $A \to K \to L$. If an
intermediate field $E$ of $L/K$ is finite unramified relative to $A$, then for every
$K$-algebra automorphism $\sigma$ of $L$ the image $\sigma(E)$ is finite unramified relative
to $A$. -/
theorem IsFiniteUnramified.map {E : IntermediateField K L}
    (hE : IsFiniteUnramified A E) (σ : L ≃ₐ[K] L) :
    IsFiniteUnramified A (E.map σ.toAlgHom) := by
  obtain ⟨hfin, hunr⟩ := hE
  constructor
  · exact LinearEquiv.finiteDimensional
      (IntermediateField.intermediateFieldMap σ E).toLinearEquiv
  · let e : E ≃ₐ[A] E.map (σ : L →ₐ[K] L) :=
      (IntermediateField.intermediateFieldMap σ E).restrictScalars A
    exact Algebra.FormallyUnramified.of_equiv e.mapIntegralClosure

private theorem map_maximalUnramifiedSubextension_le (σ : L ≃ₐ[K] L) :
    (maximalUnramifiedSubextension A K L).map σ.toAlgHom ≤
      maximalUnramifiedSubextension A K L := by
  unfold maximalUnramifiedSubextension
  rw [IntermediateField.map_iSup]
  apply iSup_le
  intro E
  rw [IntermediateField.map_iSup]
  apply iSup_le
  intro hE
  exact le_maximalUnramifiedSubextension (hE.map σ)

/-- **The maximal unramified subextension is stable under automorphisms.** Let $A$ be a
commutative ring and $L/K$ a field extension such that the map $A \to L$ factors as
$A \to K \to L$, and let $M$ be the maximal unramified subextension of $L/K$ relative to $A$.
For every $K$-algebra automorphism $\sigma$ of $L$, $\sigma(M) = M$. -/
theorem map_maximalUnramifiedSubextension (σ : L ≃ₐ[K] L) :
    (maximalUnramifiedSubextension A K L).map σ.toAlgHom =
      maximalUnramifiedSubextension A K L := by
  apply le_antisymm
  · exact map_maximalUnramifiedSubextension_le σ
  · intro x hx
    rw [IntermediateField.mem_map]
    have hx' : σ.symm x ∈ maximalUnramifiedSubextension A K L := by
      apply map_maximalUnramifiedSubextension_le σ.symm
      rw [IntermediateField.mem_map]
      exact ⟨x, hx, by simp⟩
    exact ⟨σ.symm x, hx', by simp⟩

end IntermediateField
