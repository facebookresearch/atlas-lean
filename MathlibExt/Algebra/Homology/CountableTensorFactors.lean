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
# Finite homogeneous factors in the original sum tensor

The native tensor degree is spanned by its actual homogeneous pure tensors.
Each native tensor element is consequently contained in the span of finitely
many such tensors, with their actual factors retained.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{u} R) ℤ)

/-- An actual homogeneous element, retaining its original integer degree. -/
abbrev HomogeneousElement := Σ n : ℤ, C.X n

/-- A pure original tensor of prescribed total degree, retaining both factors. -/
structure HomogeneousTensorTerm (n : ℤ) where
  /-- The original degree of the left factor. -/
  leftDegree : ℤ
  /-- The left factor in its original degree. -/
  left : C.X leftDegree
  /-- The right factor in the complementary degree. -/
  right : C.X (n - leftDegree)

variable [HomologicalComplex.HasTensor C C]

/-- The actual homogeneous pure tensor in the native sum-total degree. -/
def HomogeneousTensorTerm.value {n : ℤ} (t : HomogeneousTensorTerm C n) :
    (HomologicalComplex.tensorObj C C).X n :=
  (HomologicalComplex.ιTensorObj C C t.leftDegree (n - t.leftDegree) n (by omega)).hom
    (TensorProduct.tmul R t.left t.right)

/-- The left factor with its actual original degree. -/
def HomogeneousTensorTerm.leftElement {n : ℤ} (t : HomogeneousTensorTerm C n) :
    HomogeneousElement C := ⟨t.leftDegree, t.left⟩

/-- The right factor with its actual original degree. -/
def HomogeneousTensorTerm.rightElement {n : ℤ} (t : HomogeneousTensorTerm C n) :
    HomogeneousElement C := ⟨n - t.leftDegree, t.right⟩

/-- The original sum tensor degree is spanned by actual homogeneous pure tensors. -/
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

/-- Every native tensor element uses finitely many actual homogeneous pure tensors. -/
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

/-- Choose a finite actual decomposition-support for each original tensor element. -/
def finiteHomogeneousTensorTerms {n : ℤ}
    (z : (HomologicalComplex.tensorObj C C).X n) : Finset (HomogeneousTensorTerm C n) :=
  (exists_finite_homogeneousTensorTerms C n z).choose

lemma finiteHomogeneousTensorTerms_spec {n : ℤ}
    (z : (HomologicalComplex.tensorObj C C).X n) :
    z ∈ Submodule.span R ((HomogeneousTensorTerm.value C) ''
      (finiteHomogeneousTensorTerms C z : Set (HomogeneousTensorTerm C n))) :=
  (exists_finite_homogeneousTensorTerms C n z).choose_spec

end CochainComplex
