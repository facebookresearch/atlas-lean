/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompactSeparable
import MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteColimit

/-!
# Compact separable CGWH sources on closed ordinal diagrams

The actual filtered closed CGWH cocone remains colimiting in TopCat. Compact
separable maps factor through a stage of a bottomed linear closed diagram;
closed T1 embeddings give uniqueness. The realized boundary and horn generator
families retain compact separable domains and codomains.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty Topology TopologicalSpace SSet
open scoped Simplicial

namespace CGWH

/-- The original filtered closed cocone remains colimiting after the
actual TopCat inclusion, by the proved injective-diagram CGWH comparison. -/
def originalClosedCoconeIsColimitTop
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (F : J ⥤ CGWH.{u, v})
    (hF : ∀ ⦃a b : J⦄ (f : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (c : Cocone F) (hc : IsColimit c) : IsColimit (CGWH.cgwhToTop.mapCocone c) := by
  have hW := CGWH.compactlyGeneratedColimit_isWeakHausdorff_of_maps_injective F
    (fun _ _ f => (hF f).injective)
  have hK := CGWH.isColimitMapCoconeOfWeakHausdorff F c hc hW
  exact isColimitOfPreserves CompactlyGenerated.compactlyGeneratedToTop hK

/-- Compact separable Hom preserves the actual colimit of each bottomed
linear closed diagram. The source and target are the original objects. -/
theorem compactSeparable_preservesClosedLinearColimit
    (A : CGWH.{u, v}) [CompactSpace A] [SeparableSpace A]
    {O : Type v} [LinearOrder O] [OrderBot O] (F : O ⥤ CGWH.{u, v})
    (hF : ∀ ⦃a b : O⦄ (f : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (F.map f))) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) := by
  let T := CGWH.cgwhToTop.{u, v}
  let full := Functor.FullyFaithful.ofFullyFaithful T
  let _ : CompactSpace (T.obj A) := by
    change CompactSpace A
    infer_instance
  let _ : SeparableSpace (T.obj A) := by
    change SeparableSpace A
    infer_instance
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  have hcTop : IsColimit (T.mapCocone c) := originalClosedCoconeIsColimitTop F hF c hc
  have hT1 : ∀ ⦃a b : O⦄ (f : a ⟶ b), TopCat.closedT1Embeddings ((F ⋙ T).map f) := by
    intro a b f
    exact { toIsClosedEmbedding := hF f
            isClosed_singleton_of_notMem_range := fun y _ => by
              change IsClosed ({y} : Set (F.obj b))
              exact isClosed_singleton }
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro f
    obtain ⟨j, g, hg⟩ := TopCat.exists_stage_of_compact_transfinite
      (T.mapCocone c) hcTop hT1 isCompact_univ (T.map f).hom
    let gj : A ⟶ F.obj j := full.preimage (TopCat.ofHom g)
    have hcomp : gj ≫ c.ι.app j = f := by
      apply T.map_injective
      rw [T.map_comp]
      change T.map (full.preimage (TopCat.ofHom g)) ≫ T.map (c.ι.app j) = T.map f
      have hmap : T.map gj = TopCat.ofHom g := full.map_preimage (TopCat.ofHom g)
      exact (congrArg (fun q : T.obj A ⟶ T.obj (F.obj j) => q ≫ T.map (c.ι.app j)) hmap).trans
        (TopCat.hom_ext hg)
    exact ⟨j, gj, by simpa using hcomp.symm⟩
  · intro j x y hxy
    have he : x ≫ c.ι.app j = y ≫ c.ι.app j := by simpa using hxy
    have hLeg : IsClosedEmbedding (T.map (c.ι.app j)).hom :=
      TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding
        (T.mapCocone c) hcTop hF j
    have hEq : x = y := by
      apply T.map_injective
      apply TopCat.hom_ext
      ext a
      apply hLeg.injective
      exact ConcreteCategory.congr_hom (T.congr_map he) a
    exact ⟨j, 𝟙 j, by simpa using hEq⟩

/-- Original source Hom retains every leg of the caller's closed linear
colimit cocone. -/
def mappedOriginalCompactSourceCocone
    (A : CGWH.{u, v}) [CompactSpace A] [SeparableSpace A]
    {O : Type v} [LinearOrder O] [OrderBot O] (F : O ⥤ CGWH.{u, v})
    (hF : ∀ ⦃a b : O⦄ (f : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (Opposite.op A)).mapCocone c) := by
  let _ := compactSeparable_preservesClosedLinearColimit A F hF
  exact isColimitOfPreserves _ hc

private theorem compactSeparable_of_iso {A B : CGWH.{u, v}} (e : A ≅ B)
    (hB : CompactSpace B ∧ SeparableSpace B) : CompactSpace A ∧ SeparableSpace A := by
  let _ : CompactSpace B := hB.1
  let _ : SeparableSpace B := hB.2
  let h := TopCat.homeoOfIso (CGWH.cgwhToTop.mapIso e)
  let _ : CompactSpace (CGWH.cgwhToTop.obj B) := by
    change CompactSpace B
    exact hB.1
  let _ : SeparableSpace (CGWH.cgwhToTop.obj B) := by
    change SeparableSpace B
    exact hB.2
  exact ⟨h.symm.compactSpace, h.symm.surjective.denseRange.separableSpace h.symm.continuous⟩

/-- Actual realized boundary/horn arrows retain compact separable domains
and codomains, transported through their original whole-Arrow equality. -/
theorem realizedGeneratorEndpoints_compactSeparable {A B : CGWH.{u, v}} (g : A ⟶ B)
    (hg : (CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) g) :
    (CompactSpace A ∧ SeparableSpace A) ∧ (CompactSpace B ∧ SeparableSpace B) := by
  rw [MorphismProperty.sup_iff] at hg
  rcases hg with hg | hg
  · rw [CGWH.realizedBoundaryInclusions, MorphismProperty.ofHoms_iff] at hg
    obtain ⟨n, he⟩ := hg
    let e := eqToIso he
    exact ⟨compactSeparable_of_iso (Arrow.leftFunc.mapIso e)
        (finiteCGWHRealization_compactSeparable.{u, v} (SSet.boundary n)),
      compactSeparable_of_iso (Arrow.rightFunc.mapIso e)
        (finiteCGWHRealization_compactSeparable.{u, v} (SSet.stdSimplex.obj ⦋n⦌))⟩
  · rw [CGWH.realizedHornInclusions, MorphismProperty.iSup_iff] at hg
    obtain ⟨n, hn⟩ := hg
    rw [MorphismProperty.ofHoms_iff] at hn
    obtain ⟨i, he⟩ := hn
    let e := eqToIso he
    exact ⟨compactSeparable_of_iso (Arrow.leftFunc.mapIso e)
        (finiteCGWHRealization_compactSeparable.{u, v} (SSet.horn (n + 1) i)),
      compactSeparable_of_iso (Arrow.rightFunc.mapIso e)
        (finiteCGWHRealization_compactSeparable.{u, v} (SSet.stdSimplex.obj ⦋n + 1⦌))⟩


end CGWH
