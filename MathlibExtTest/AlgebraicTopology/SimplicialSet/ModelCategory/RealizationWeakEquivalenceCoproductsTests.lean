/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts

/-!
# Realization weak-equivalence coproduct tests

These tests pin binary, finite, and arbitrary coproduct closure and the
packaged same-universe morphism-property instance. They make no filtered
colimit, model-category, or Bousfield--Kan claim.
-/

open CategoryTheory Limits MorphismProperty

universe u v

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproductsTests

/-- Binary closure retains the two component maps in left/right order. -/
example {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : SSet.realizationWeakEquivalences f)
    (hg : SSet.realizationWeakEquivalences g) :
    SSet.realizationWeakEquivalences (coprod.map f g) :=
  SSet.coprod_map_mem_realizationWeakEquivalences f g hf hg

/-- The finite theorem covers a genuine three-summand family. -/
example {X Y : Fin 3 → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f hf

/-- Finite closure allows an index universe independent of the simplicial
universe. -/
example {ι : Type v} [Finite ι] {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f hf

/-- Arbitrary same-universe families use the filtered finite-subcoproduct
construction. -/
example {ι : Type u} {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences f hf

/-- The public coproduct-stability instance is available to generic clients. -/
example :
    SSet.realizationWeakEquivalences.{u}.IsStableUnderCoproducts.{u} :=
  inferInstance

/-- The generic `colimMap` API sees the same arbitrary coproduct closure. -/
example {ι : Type u} {X Y : Discrete ι ⥤ SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.realizationWeakEquivalences.functorCategory (Discrete ι) f) :
    SSet.realizationWeakEquivalences (colimMap f) :=
  MorphismProperty.colimMap f hf

/-- The empty coproduct boundary is covered by the finite theorem. -/
example {X Y : Fin 0 → SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f
    (fun i => Fin.elim0 i)

section UniverseOne

example {A B C D : SSet.{1}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : SSet.realizationWeakEquivalences f)
    (hg : SSet.realizationWeakEquivalences g) :
    SSet.realizationWeakEquivalences (coprod.map f g) :=
  SSet.coprod_map_mem_realizationWeakEquivalences f g hf hg

example {X Y : Fin 3 → SSet.{1}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f hf

example {ι : Type 1} {X Y : ι → SSet.{1}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences f hf

example :
    SSet.realizationWeakEquivalences.{1}.IsStableUnderCoproducts.{1} :=
  inferInstance

example {X Y : Fin 0 → SSet.{1}} (f : ∀ i, X i ⟶ Y i) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f
    (fun i => Fin.elim0 i)

end UniverseOne

section UniverseZero

example {A B C D : SSet.{0}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : SSet.realizationWeakEquivalences f)
    (hg : SSet.realizationWeakEquivalences g) :
    SSet.realizationWeakEquivalences (coprod.map f g) :=
  SSet.coprod_map_mem_realizationWeakEquivalences f g hf hg

example {X Y : Fin 3 → SSet.{0}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f hf

example {ι : Type} {X Y : ι → SSet.{0}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, SSet.realizationWeakEquivalences (f i)) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences f hf

example :
    SSet.realizationWeakEquivalences.{0}.IsStableUnderCoproducts.{0} :=
  inferInstance

example {X Y : Fin 0 → SSet.{0}} (f : ∀ i, X i ⟶ Y i) :
    SSet.realizationWeakEquivalences (Limits.Sigma.map f) :=
  SSet.sigma_map_mem_realizationWeakEquivalences_of_finite f
    (fun i => Fin.elim0 i)

end UniverseZero

section ShapeBoundary

example (_ι : Type 1) : True := by
  fail_if_success
    let _ : SSet.realizationWeakEquivalences.{0}.
        IsStableUnderCoproductsOfShape _ι := inferInstance
  trivial

end ShapeBoundary

#print axioms SSet.coprod_map_mem_realizationWeakEquivalences
#print axioms SSet.sigma_map_mem_realizationWeakEquivalences_of_finite
#print axioms SSet.sigma_map_mem_realizationWeakEquivalences
#print axioms SSet.realizationWeakEquivalences_isStableUnderCoproducts

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproductsTests
