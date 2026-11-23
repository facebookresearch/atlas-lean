/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CompactlyGenerated.ClosedEmbeddingProduct

/-!
# Tests for closed embeddings and native products

These owners exercise symbolic use, coordinate coherence, identity and
proper closed inclusions, universe polymorphism, privacy, standard trust,
and the nonclosed-embedding boundary.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

universe u v

namespace MathlibExtTest.CompactlyGenerated.ClosedEmbeddingProduct

#check @CompactlyGenerated.isClosedEmbedding_prodMap

section Symbolic

variable {A B C D : CompactlyGenerated.{u, v}}
variable (f : A ⟶ B) (g : C ⟶ D)
variable (hf : IsClosedEmbedding (ConcreteCategory.hom f))
variable (hg : IsClosedEmbedding (ConcreteCategory.hom g))

example : IsClosedEmbedding (ConcreteCategory.hom (f ⊗ₘ g)) :=
  CompactlyGenerated.isClosedEmbedding_prodMap f g hf hg

example :
    CompactlyGenerated.compactlyGeneratedToTop.map (f ⊗ₘ g) ≫
        CompactlyGenerated.prodComparisonToTop B D ≫ Limits.prod.fst =
      CompactlyGenerated.prodComparisonToTop A C ≫ Limits.prod.fst ≫
        CompactlyGenerated.compactlyGeneratedToTop.map f := by
  let I := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  have hBD : CompactlyGenerated.prodComparisonToTop B D ≫
      Limits.prod.fst =
      I.map (CartesianMonoidalCategory.fst B D) := by
    unfold CompactlyGenerated.prodComparisonToTop
    exact Limits.prod.lift_fst _ _
  have hAC : CompactlyGenerated.prodComparisonToTop A C ≫
      Limits.prod.fst ≫ I.map f =
      I.map (CartesianMonoidalCategory.fst A C) ≫ I.map f := by
    unfold CompactlyGenerated.prodComparisonToTop
    exact Limits.prod.lift_fst_assoc _ _ _
  calc
    _ = I.map (f ⊗ₘ g) ≫
        I.map (CartesianMonoidalCategory.fst B D) := by rw [hBD]
    _ = I.map
        ((f ⊗ₘ g) ≫ CartesianMonoidalCategory.fst B D) := by
      rw [I.map_comp]
    _ = I.map
        (CartesianMonoidalCategory.fst A C ≫ f) := by
      rw [CartesianMonoidalCategory.tensorHom_fst]
    _ = I.map (CartesianMonoidalCategory.fst A C) ≫ I.map f := by
      rw [I.map_comp]
    _ = _ := hAC.symm

example :
    CompactlyGenerated.compactlyGeneratedToTop.map (f ⊗ₘ g) ≫
        CompactlyGenerated.prodComparisonToTop B D ≫ Limits.prod.snd =
      CompactlyGenerated.prodComparisonToTop A C ≫ Limits.prod.snd ≫
        CompactlyGenerated.compactlyGeneratedToTop.map g := by
  let I := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  have hBD : CompactlyGenerated.prodComparisonToTop B D ≫
      Limits.prod.snd =
      I.map (CartesianMonoidalCategory.snd B D) := by
    unfold CompactlyGenerated.prodComparisonToTop
    exact Limits.prod.lift_snd _ _
  have hAC : CompactlyGenerated.prodComparisonToTop A C ≫
      Limits.prod.snd ≫ I.map g =
      I.map (CartesianMonoidalCategory.snd A C) ≫ I.map g := by
    unfold CompactlyGenerated.prodComparisonToTop
    exact Limits.prod.lift_snd_assoc _ _ _
  calc
    _ = I.map (f ⊗ₘ g) ≫
        I.map (CartesianMonoidalCategory.snd B D) := by rw [hBD]
    _ = I.map
        ((f ⊗ₘ g) ≫ CartesianMonoidalCategory.snd B D) := by
      rw [I.map_comp]
    _ = I.map
        (CartesianMonoidalCategory.snd A C ≫ g) := by
      rw [CartesianMonoidalCategory.tensorHom_snd]
    _ = I.map (CartesianMonoidalCategory.snd A C) ≫ I.map g := by
      rw [I.map_comp]
    _ = _ := hAC.symm

example : IsClosedEmbedding
    (ConcreteCategory.hom ((𝟙 A) ⊗ₘ (𝟙 C))) :=
  CompactlyGenerated.isClosedEmbedding_prodMap (𝟙 A) (𝟙 C)
    IsClosedEmbedding.id IsClosedEmbedding.id

end Symbolic

section ProperClosedInclusion

private abbrev X : CompactlyGenerated.{0, 0} := CompactlyGenerated.of PUnit
private abbrev Y : CompactlyGenerated.{0, 0} := CompactlyGenerated.of Bool
private noncomputable def pointInclusion : X ⟶ Y :=
  CompactlyGenerated.ofHom
    ⟨fun _ => false, continuous_of_discreteTopology⟩

private theorem pointInclusion_isClosedEmbedding :
    IsClosedEmbedding (ConcreteCategory.hom pointInclusion) := by
  apply Continuous.isClosedEmbedding
  · exact continuous_of_discreteTopology
  · intro x y _
    exact Subsingleton.elim x y

example : IsClosedEmbedding
    (ConcreteCategory.hom (pointInclusion ⊗ₘ (𝟙 X))) :=
  CompactlyGenerated.isClosedEmbedding_prodMap pointInclusion (𝟙 X)
    pointInclusion_isClosedEmbedding IsClosedEmbedding.id

end ProperClosedInclusion

section NonclosedBoundary

example : IsEmbedding ((↑) : Set.Iio (0 : ℝ) → ℝ) :=
  Topology.IsEmbedding.subtypeVal

example : ¬ IsClosedEmbedding ((↑) : Set.Iio (0 : ℝ) → ℝ) := by
  intro h
  have hClosed : IsClosed (Set.Iio (0 : ℝ)) := by
    simpa only [Subtype.range_val] using h.isClosed_range
  have hZero : (0 : ℝ) ∈ Set.Iio 0 := by
    rw [← hClosed.closure_eq, closure_Iio]
    simp
  exact (lt_irrefl 0) (show (0 : ℝ) < 0 from hZero)

end NonclosedBoundary

section UniverseMatrix

#check @CompactlyGenerated.isClosedEmbedding_prodMap.{0, 0}
#check @CompactlyGenerated.isClosedEmbedding_prodMap.{1, 1}
#check @CompactlyGenerated.isClosedEmbedding_prodMap.{0, 1}
#check @CompactlyGenerated.isClosedEmbedding_prodMap.{1, 0}

end UniverseMatrix

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.toCompactlyGenerated_map_isClosedEmbedding

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.closedEmbeddingBinaryKificationIso

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.closedEmbeddingBinaryKificationIso_hom_fst

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.closedEmbeddingBinaryKificationIso_hom_snd

#print axioms CompactlyGenerated.isClosedEmbedding_prodMap

end MathlibExtTest.CompactlyGenerated.ClosedEmbeddingProduct
