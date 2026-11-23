/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopPair

/-!
# The canonical excision map of topological pairs

Constructs the pair map from `(B, A ∩ B)` to `(X, A)` with its ambient and
subspace inclusions. The usual closure-inside-interior condition implies the
corresponding interiors-cover condition for a complementary set.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace TopPair

variable (X : TopCat.{u}) (A B : Set X)

/-- Inclusion `A ∩ B → B`, used in the excision source pair. -/
noncomputable def excisionSourceMap : TopCat.of ↑(A ∩ B) ⟶ TopCat.of ↑B :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.2⟩, by fun_prop⟩

/-- Inclusion `B → X`, used by the excision morphism. -/
noncomputable def excisionAmbientMap : TopCat.of ↑B ⟶ X :=
  TopCat.ofHom ⟨fun x => x.1, by fun_prop⟩

/-- Inclusion `A ∩ B → A`, used by the excision morphism. -/
noncomputable def excisionSubspaceMap : TopCat.of ↑(A ∩ B) ⟶ TopCat.of ↑A :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.1⟩, by fun_prop⟩

/-- The source pair `(B, A ∩ B)` of the canonical excision morphism. -/
noncomputable def excisionSource : TopPair.{u} :=
  TopPair.of (excisionSourceMap X A B)
    (by
      let f : ↑(A ∩ B) → ↑B := fun x => ⟨x.1, x.2.2⟩
      let g : ↑B → X := fun x => x.1
      have hf : Continuous f := by fun_prop
      have hg : Continuous g := by fun_prop
      have hgf : Topology.IsEmbedding (g ∘ f) := by
        have hEq : g ∘ f = fun x : ↑(A ∩ B) => (x.1 : X) := by
          funext x
          rfl
        rw [hEq]
        exact Topology.IsEmbedding.subtypeVal
      change Topology.IsEmbedding f
      exact Topology.IsEmbedding.of_comp hf hg hgf)

/-- The target pair `(X, A)` of the canonical excision morphism. -/
noncomputable def excisionTarget : TopPair.{u} := TopPair.ofSubset A

/-- The canonical excision morphism `(B, A ∩ B) ⟶ (X, A)`. -/
noncomputable def excisionHom : excisionSource X A B ⟶ excisionTarget X A :=
  TopPair.ofHom (excisionAmbientMap X B) (excisionSubspaceMap X A B)
    (by
      apply TopCat.hom_ext
      ext x
      rfl)

/-- The usual closure hypothesis implies the interiors-cover hypothesis with `B = Uᶜ`. -/
lemma interiorsCover_compl_of_closure_subset_interior (U : Set X)
    (h : closure U ⊆ interior A) :
    (Set.univ : Set X) ⊆ interior A ∪ interior Uᶜ := by
  intro x _
  by_cases hx : x ∈ closure U
  · exact Set.mem_union_left _ (h hx)
  · rw [interior_compl]
    exact Set.mem_union_right _ hx

end TopPair
