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

public import MathlibExt.Algebra.Homology.CountableTensorFactors
public import MathlibExt.Algebra.Homology.HomogeneousSubcomplex
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Countably many homogeneous generators closed under differential and comultiplication

The closure operation retains actual finite original tensor factors. The
degreewise spans form an honest subcomplex. Over a field its total collection
of basis vectors is countable, including all integer degrees together.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]
variable (C : CochainComplex (ModuleCat.{u} R) ℤ)
  (Δ : C ⟶ HomologicalComplex.tensorObj C C)

/-- One closure step adds the actual differential and both factors of a finite original tensor
support. -/
def dgCoalgebraNeighbors (x : HomogeneousElement C) : Finset (HomogeneousElement C) := by
  classical
  exact insert ⟨x.1 + 1, (C.d x.1 (x.1 + 1)).hom x.2⟩
    ((finiteHomogeneousTensorTerms C ((Δ.f x.1).hom x.2)).biUnion (fun t =>
      {HomogeneousTensorTerm.leftElement C t, HomogeneousTensorTerm.rightElement C t}))

/-- Countable iteration of the actual differential and original finite comultiplication factors. -/
def dgCoalgebraClosure (s : Set (HomogeneousElement C)) : Set (HomogeneousElement C) :=
  Set.finiteClosure (dgCoalgebraNeighbors C Δ) s

lemma dgCoalgebraClosure_countable {s : Set (HomogeneousElement C)} (hs : s.Countable) :
    (dgCoalgebraClosure C Δ s).Countable := hs.finiteClosure _

lemma subset_dgCoalgebraClosure (s : Set (HomogeneousElement C)) : s ⊆ dgCoalgebraClosure C Δ s :=
  Set.subset_finiteClosure _ _

lemma dgCoalgebraClosure_d_mem {s : Set (HomogeneousElement C)}
    {n : ℤ} {x : C.X n} (hx : (⟨n, x⟩ : HomogeneousElement C) ∈ dgCoalgebraClosure C Δ s) :
    (⟨n + 1, (C.d n (n + 1)).hom x⟩ : HomogeneousElement C) ∈ dgCoalgebraClosure C Δ s := by
  classical
  apply Set.finiteClosure_closed _ _ hx
  exact Finset.mem_insert_self _ _

lemma dgCoalgebraClosure_factors_mem {s : Set (HomogeneousElement C)}
    {n : ℤ} {x : C.X n} (hx : (⟨n, x⟩ : HomogeneousElement C) ∈ dgCoalgebraClosure C Δ s)
    (t : HomogeneousTensorTerm C n) (ht : t ∈ finiteHomogeneousTensorTerms C ((Δ.f n).hom x)) :
    HomogeneousTensorTerm.leftElement C t ∈ dgCoalgebraClosure C Δ s ∧
      HomogeneousTensorTerm.rightElement C t ∈ dgCoalgebraClosure C Δ s := by
  classical
  constructor <;> apply Set.finiteClosure_closed _ _ hx
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩)
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩)

/-- Actual closure generators in one original integer degree. -/
def dgCoalgebraDegreeGenerators (s : Set (HomogeneousElement C)) (n : ℤ) : Set (C.X n) :=
  (fun x => (⟨n, x⟩ : HomogeneousElement C)) ⁻¹' dgCoalgebraClosure C Δ s

lemma dgCoalgebraDegreeGenerators_countable {s : Set (HomogeneousElement C)} (hs : s.Countable)
    (n : ℤ) : (dgCoalgebraDegreeGenerators C Δ s n).Countable :=
  (dgCoalgebraClosure_countable C Δ hs).preimage (by
    intro x y h
    cases h
    rfl)

/-- The span is taken over the entire coefficient field or ring. Its carrier need not be
countable. -/
def dgCoalgebraDegreeSpan (s : Set (HomogeneousElement C)) (n : ℤ) : Submodule R (C.X n) :=
  Submodule.span R (dgCoalgebraDegreeGenerators C Δ s n)

lemma dgCoalgebraDegreeSpan_d_mem (s : Set (HomogeneousElement C)) (n : ℤ)
    (x : C.X n) (hx : x ∈ dgCoalgebraDegreeSpan C Δ s n) :
    (C.d n (n + 1)).hom x ∈ dgCoalgebraDegreeSpan C Δ s (n + 1) := by
  have h : dgCoalgebraDegreeSpan C Δ s n ≤
      (dgCoalgebraDegreeSpan C Δ s (n + 1)).comap (C.d n (n + 1)).hom := by
    apply Submodule.span_le.mpr
    intro y hy
    exact Submodule.subset_span (dgCoalgebraClosure_d_mem C Δ hy)
  exact h hx

/-- Honest original subcomplex obtained from the degreewise spans of the countable closure. -/
def dgCoalgebraClosureSubcomplex (s : Set (HomogeneousElement C)) : HomogeneousSubcomplex C where
  piece := dgCoalgebraDegreeSpan C Δ s
  d_mem := dgCoalgebraDegreeSpan_d_mem C Δ s

section FieldBasis

/-- A countable total collection of homogeneous basis vectors, over every original integer
degree. -/
structure CountableHomogeneousBasis (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The index type of the basis in each original degree. -/
  index : ℤ → Type u
  /-- The basis of the carrier component of each original degree. -/
  basis : ∀ n : ℤ, Module.Basis (index n) R (K.X n)
  countable : Countable (Σ n : ℤ, index n)

variable {F : Type u} [Field F]

/-- Choose an actual linearly independent subset of the given generators spanning the same
module. -/
def countableSpanBasisSet {M : Type u} [AddCommGroup M] [Module F M] (g : Set M) : Set M :=
  (exists_linearIndependent F g).choose

lemma countableSpanBasisSet_subset {M : Type u} [AddCommGroup M] [Module F M] (g : Set M) :
    countableSpanBasisSet (F := F) g ⊆ g := (exists_linearIndependent F g).choose_spec.1

/-- Basis of the honest original span, with index among the original generators. -/
def countableSpanBasis {M : Type u} [AddCommGroup M] [Module F M] (g : Set M) :
    Module.Basis (countableSpanBasisSet (F := F) g) F (Submodule.span F g) := by
  let h := (exists_linearIndependent F g).choose_spec
  exact (Module.Basis.span h.2.2).map (LinearEquiv.ofEq _ _ (by simpa using h.2.1))

/-- Countability of the actual chosen basis index follows from the generator set alone. -/
lemma countableSpanBasisSet_countable {M : Type u} [AddCommGroup M] [Module F M]
    {g : Set M} (hg : g.Countable) : (countableSpanBasisSet (F := F) g).Countable :=
  hg.mono (countableSpanBasisSet_subset g)
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} F), GradedObject.HasTensor X Y]

/-- The countable original homogeneous closure has a countable TOTAL basis, even over an
uncountable field. -/
def dgCoalgebraClosureCountableHomogeneousBasis
    (K : CochainComplex (ModuleCat.{u} F) ℤ) (δ : K ⟶ HomologicalComplex.tensorObj K K)
    (s : Set (HomogeneousElement K)) (hs : s.Countable) :
    CountableHomogeneousBasis ((dgCoalgebraClosureSubcomplex K δ s).complex) := by
  let g := dgCoalgebraDegreeGenerators K δ s
  let I : ℤ → Type u := fun n => countableSpanBasisSet (F := F) (g n)
  letI : ∀ n : ℤ, Countable (I n) := fun n =>
    (countableSpanBasisSet_countable (dgCoalgebraDegreeGenerators_countable K δ hs n)).to_subtype
  exact { index := I, basis := fun n => countableSpanBasis (g n), countable := inferInstance }

end FieldBasis

end CochainComplex
