/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.Quotient.Basic
public import MathlibExt.Data.Set.CountableFiniteClosure

/-!
# Finite homogeneous supports in a cochain tensor product

Let C be an integer cochain complex of modules over a commutative ring R, with its tensor
complex defined. A pure homogeneous tensor in total degree n records a left factor in degree p
and a right factor in degree n−p, followed by the antidiagonal coprojection.

These pure tensors span the degree-n tensor module. Every element therefore lies in the R-span
of a finite set of such terms. Choosing a finite support retains the actual factors and their
degrees; the coefficients remain arbitrary elements of R.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{u} R) ℤ)

/-- An element with its integer homogeneous degree.

A homogeneous element is a pair (n,x) with n ∈ ℤ and x ∈ C_n. -/
abbrev HomogeneousElement := Σ n : ℤ, C.X n

/-- A pure tensor with prescribed total degree.

A term in degree n consists of a left degree p, a left factor in C_p and a right factor in
C_{n−p}. -/
structure HomogeneousTensorTerm (n : ℤ) where
  /-- The integer degree of a pure tensor's left factor.

This p ∈ ℤ determines the two component degrees p and n−p. -/
  leftDegree : ℤ
  /-- The left homogeneous tensor factor.

The left factor lies in C_p at the recorded left degree. -/
  left : C.X leftDegree
  /-- The right homogeneous tensor factor.

The right factor lies in C_{n−p}, complementary to the left degree. -/
  right : C.X (n - leftDegree)

variable [HomologicalComplex.HasTensor C C]

/-- The value of a homogeneous tensor term in the total tensor degree.

Take the pure tensor of its two factors and apply the antidiagonal coprojection C_p ⊗ C_{n−p}
→ (C ⊗ C)_n. -/
def HomogeneousTensorTerm.value {n : ℤ} (t : HomogeneousTensorTerm C n) :
    (HomologicalComplex.tensorObj C C).X n :=
  (HomologicalComplex.ιTensorObj C C t.leftDegree (n - t.leftDegree) n (by omega)).hom
    (TensorProduct.tmul R t.left t.right)

/-- The left factor as a homogeneous element.

Retain the left factor together with its integer degree p. -/
def HomogeneousTensorTerm.leftElement {n : ℤ} (t : HomogeneousTensorTerm C n) :
    HomogeneousElement C := ⟨t.leftDegree, t.left⟩

/-- The right factor as a homogeneous element.

Retain the right factor together with its integer degree n−p. -/
def HomogeneousTensorTerm.rightElement {n : ℤ} (t : HomogeneousTensorTerm C n) :
    HomogeneousElement C := ⟨n - t.leftDegree, t.right⟩

/-- Homogeneous pure tensors span the total tensor degree.

For every n ∈ ℤ, the R-span of the values of all homogeneous tensor terms is the full degree-n
tensor module. -/
theorem homogeneousTensorTerms_span (n : ℤ) :
    Submodule.span R (Set.range (HomogeneousTensorTerm.value (C := C) (n := n))) = ⊤ := by
  let S : Submodule R ((HomologicalComplex.tensorObj C C).X n) :=
    Submodule.span R (Set.range (HomogeneousTensorTerm.value (C := C) (n := n)))
  let Q := ModuleCat.of R (((HomologicalComplex.tensorObj C C).X n) ⧸ S)
  let q : (HomologicalComplex.tensorObj C C).X n ⟶ Q := ModuleCat.ofHom S.mkQ
  have hq : q = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    change i + j = n at hij
    have hj : j = n - i := by omega
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change S.mkQ ((HomologicalComplex.ιTensorObj C C i (n - i) n hij).hom z) = 0
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      apply (Submodule.Quotient.mk_eq_zero S).mpr
      exact Submodule.subset_span ⟨⟨i, a, b⟩, rfl⟩
    | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  exact congrArg (fun f : (HomologicalComplex.tensorObj C C).X n ⟶ Q => f.hom z) hq

/-- Every tensor element has finite homogeneous spanning support.

For z in total degree n, there is a finite set of homogeneous tensor terms whose values have z
in their R-span. -/
theorem exists_finite_homogeneousTensorTerms (n : ℤ)
    (z : (HomologicalComplex.tensorObj C C).X n) :
    ∃ t : Finset (HomogeneousTensorTerm C n),
      z ∈ Submodule.span R
        ((HomogeneousTensorTerm.value C) '' (t : Set (HomogeneousTensorTerm C n))) := by
  classical
  have hz : z ∈ Submodule.span R
      (Set.range (HomogeneousTensorTerm.value (C := C) (n := n))) := by
    rw [homogeneousTensorTerms_span C n]
    trivial
  refine Submodule.span_induction (fun y hy => ?_) ?_ ?_ ?_ hz
  · rcases hy with ⟨t, rfl⟩
    refine ⟨{t}, Submodule.subset_span ?_⟩
    exact ⟨t, Finset.mem_singleton_self t, rfl⟩
  · exact ⟨∅, Submodule.zero_mem _⟩
  · rintro y z _ _ ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, Submodule.add_mem _ ?_ ?_⟩
    · exact Submodule.span_mono (Set.image_mono (by simp)) hs
    · exact Submodule.span_mono (Set.image_mono (by simp)) ht
  · rintro a y _ ⟨t, ht⟩
    exact ⟨t, Submodule.smul_mem _ a ht⟩

/-- A chosen finite homogeneous tensor support.

Choose a finite set of actual factor pairs spanning the given tensor element. -/
def finiteHomogeneousTensorTerms {n : ℤ}
    (z : (HomologicalComplex.tensorObj C C).X n) : Finset (HomogeneousTensorTerm C n) :=
  (exists_finite_homogeneousTensorTerms C n z).choose

/-- The chosen homogeneous support spans its tensor element.

The tensor element belongs to the R-span of the values of finiteHomogeneousTensorTerms. -/
lemma finiteHomogeneousTensorTerms_spec {n : ℤ}
    (z : (HomologicalComplex.tensorObj C C).X n) :
    z ∈ Submodule.span R ((HomogeneousTensorTerm.value C) ''
      (finiteHomogeneousTensorTerms C z : Set (HomogeneousTensorTerm C n))) :=
  (exists_finite_homogeneousTensorTerms C n z).choose_spec

end CochainComplex
