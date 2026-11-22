/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Colimits
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding

/-!
# Closed pushouts in CGWH

The immediate inclusion of CGWH spaces into compactly generated spaces
preserves a pushout whose first map is a closed embedding after inclusion
into topological spaces.  The opposite chosen pushout leg is again a closed
embedding.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology

universe u v

namespace CGWH

/-- The inclusion into compactly generated spaces preserves a pushout whose
first map is a closed embedding after inclusion into topological spaces. -/
theorem preservesPushout_of_isClosedEmbedding
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (CGWH.cgwhToTop.map i))) :
    PreservesColimit (span i f) CGWH.cgwhToCompactlyGenerated := by
  let j := CGWH.cgwhToCompactlyGenerated
  let k := CompactlyGenerated.compactlyGeneratedToTop
  let pJ := pushoutComparison j i f
  let pk := pushoutComparison k (j.map i) (j.map f)
  let pTop := pushoutComparison CGWH.cgwhToTop i f
  have hcomp : pTop = pk ≫ k.map pJ := by
    dsimp [pTop, pk, pJ, j, k]
    apply pushout.hom_ext
    · rw [inl_comp_pushoutComparison]
      change k.map (j.map (pushout.inl i f)) =
        (pushout.inl (k.map (j.map i)) (k.map (j.map f)) ≫ pk) ≫
          k.map pJ
      rw [inl_comp_pushoutComparison]
      rw [← Functor.map_comp, inl_comp_pushoutComparison]
    · rw [inr_comp_pushoutComparison]
      change k.map (j.map (pushout.inr i f)) =
        (pushout.inr (k.map (j.map i)) (k.map (j.map f)) ≫ pk) ≫
          k.map pJ
      rw [inr_comp_pushoutComparison]
      rw [← Functor.map_comp, inr_comp_pushoutComparison]
  have hclosed : pTop = (CGWH.pushoutClosedComparisonIso i f hi).hom := by
    dsimp [pTop]
    apply pushout.hom_ext
    · rw [inl_comp_pushoutComparison,
        CGWH.pushoutClosedComparisonIso_hom_inl]
    · rw [inr_comp_pushoutComparison,
        CGWH.pushoutClosedComparisonIso_hom_inr]
  let _ : IsIso pTop := by
    rw [hclosed]
    infer_instance
  let _ : PreservesColimitsOfSize k :=
    CompactlyGenerated.adj.leftAdjoint_preservesColimits
  let _ : IsIso pk := by
    dsimp [pk]
    infer_instance
  let _ : IsIso (pk ≫ k.map pJ) := by
    rw [← hcomp]
    infer_instance
  let _ : IsIso (k.map pJ) :=
    IsIso.of_isIso_comp_left pk (k.map pJ)
  let _ : IsIso pJ :=
    CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.isIso_of_isIso_map pJ
  exact PreservesPushout.of_iso_comparison (G := j)

/-- In a pushout along a closed embedding, the opposite chosen pushout leg
is a closed embedding after inclusion into compactly generated spaces. -/
theorem isClosedEmbedding_pushout_inr
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (CGWH.cgwhToTop.map i))) :
    IsClosedEmbedding
      (ConcreteCategory.hom
        (CGWH.cgwhToCompactlyGenerated.map (pushout.inr i f))) := by
  let e := CGWH.pushoutClosedComparisonIso i f hi
  have hraw : IsClosedEmbedding
      (ConcreteCategory.hom
        (pushout.inr (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map f))) :=
    TopCat.isClosedEmbedding_of_isPushout
      (IsPushout.of_hasPushout
        (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map f)) hi
  have hcomp : IsClosedEmbedding
      (ConcreteCategory.hom
        (pushout.inr (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map f) ≫ e.hom)) :=
    (TopCat.homeoOfIso e).isClosedEmbedding.comp hraw
  have hJ : IsClosedEmbedding
      (ConcreteCategory.hom
        (CGWH.cgwhToTop.map (pushout.inr i f))) := by
    rw [← CGWH.pushoutClosedComparisonIso_hom_inr i f hi]
    exact hcomp
  exact hJ

end CGWH
