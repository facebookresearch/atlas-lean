/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Code.FrontierD.SixVertexUnitComponentHall










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexDegreeTwoUnitComponentOrbitHallDecidableProp
    (p : Prop) : Decidable p :=
  Classical.propDecidable p



def SixVertexDegreeTwoUnitStrandPhysicalRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (target : SixVertexConfigurationPhysicalTarget T middle) : Prop :=
  exists hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1,
    exists seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1,
      exists hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
        source.2.2.1 hdegree seed).sum = 1,
        target = sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree
          seed hunit



theorem SixVertexDegreeTwoUnitStrandPhysicalRelated.fineRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt}
    {target : SixVertexConfigurationPhysicalTarget T middle}
    (hrelated : SixVertexDegreeTwoUnitStrandPhysicalRelated source target) :
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1) (target.1.1, target.2.1) := by
  obtain ⟨hdegree, seed, hunit, rfl⟩ := hrelated
  exact sixVertexDegreeTwoUnitStrandPhysicalTarget_fineRelated
    source hdegree seed hunit


theorem SixVertexDegreeTwoUnitStrandPhysicalRelated.layers_ne
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt}
    {target : SixVertexConfigurationPhysicalTarget T middle}
    (hrelated : SixVertexDegreeTwoUnitStrandPhysicalRelated source target) :
    target.1 ≠ target.2 := by
  obtain ⟨hdegree, seed, hunit, rfl⟩ := hrelated
  exact sixVertexDegreeTwoUnitStrandPhysicalTarget_layers_ne
    source hdegree seed hunit





structure SixVertexDegreeTwoUnitComponentOrbitPresentation
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (Component : Type*) [Fintype Component] (k : Nat) where
  component_card : Fintype.card Component = 2 * k
  sourceEmbedding :
    BooleanLayer Component (k + 1) ↪
      SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  targetEmbedding :
    BooleanLayer Component k ↪
      SixVertexConfigurationPhysicalTarget T middle
  related_iff : forall source target,
    SixVertexDegreeTwoUnitStrandPhysicalRelated
        (sourceEmbedding source) (targetEmbedding target) <->
      booleanMiddleLayerDownRelation source target

namespace SixVertexDegreeTwoUnitComponentOrbitPresentation

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Component : Type*} [Fintype Component] {k : Nat}


abbrev SourceOrbit
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :=
  Set.range orbit.sourceEmbedding


abbrev TargetOrbit
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :=
  Set.range orbit.targetEmbedding


noncomputable def sourceEquiv
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :
    BooleanLayer Component (k + 1) ≃ orbit.SourceOrbit :=
  Equiv.ofInjective orbit.sourceEmbedding orbit.sourceEmbedding.injective


noncomputable def targetEquiv
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :
    BooleanLayer Component k ≃ orbit.TargetOrbit :=
  Equiv.ofInjective orbit.targetEmbedding orbit.targetEmbedding.injective

@[simp] theorem sourceEquiv_val
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : BooleanLayer Component (k + 1)) :
    (orbit.sourceEquiv source).1 = orbit.sourceEmbedding source := by
  rfl

@[simp] theorem targetEquiv_val
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (target : BooleanLayer Component k) :
    (orbit.targetEquiv target).1 = orbit.targetEmbedding target := by
  rfl


def Related
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : orbit.SourceOrbit) (target : orbit.TargetOrbit) : Prop :=
  SixVertexDegreeTwoUnitStrandPhysicalRelated source.1 target.1



theorem related_equiv
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : BooleanLayer Component (k + 1))
    (target : BooleanLayer Component k) :
    orbit.Related (orbit.sourceEquiv source) (orbit.targetEquiv target) <->
      booleanMiddleLayerDownRelation source target := by
  exact orbit.related_iff source target


theorem exists_booleanMatching
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :
    ∃ matching : BooleanLayer Component (k + 1) →
        BooleanLayer Component k,
      Function.Injective matching ∧
        ∀ source, booleanMiddleLayerDownRelation source (matching source) := by
  have hBoolean := booleanMiddleLayerDownRelation_hall k orbit.component_card
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective
    (booleanMiddleLayerDownRelation
      (Component := Component) (k := k))).mp hBoolean


noncomputable def booleanMatching
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :
    BooleanLayer Component (k + 1) ↪ BooleanLayer Component k :=
  ⟨Classical.choose orbit.exists_booleanMatching,
    (Classical.choose_spec orbit.exists_booleanMatching).1⟩


theorem booleanMatching_related
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : BooleanLayer Component (k + 1)) :
    SixVertexDegreeTwoUnitStrandPhysicalRelated
      (orbit.sourceEmbedding source)
      (orbit.targetEmbedding (orbit.booleanMatching source)) := by
  apply (orbit.related_iff source (orbit.booleanMatching source)).2
  exact (Classical.choose_spec orbit.exists_booleanMatching).2 source


def Hall
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) : Prop :=
  forall sources : Finset orbit.SourceOrbit,
    sources.card <=
      (Finset.univ.filter fun target : orbit.TargetOrbit =>
        ∃ source ∈ sources, orbit.Related source target).card



theorem hall
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) : orbit.Hall := by
  have hBoolean := booleanMiddleLayerDownRelation_hall k orbit.component_card
  obtain ⟨matching, hinjective, hmatching⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (booleanMiddleLayerDownRelation
        (Component := Component) (k := k))).mp hBoolean
  let physicalMatching : orbit.SourceOrbit -> orbit.TargetOrbit :=
    fun source => orbit.targetEquiv (matching (orbit.sourceEquiv.symm source))
  have hphysicalInjective : Function.Injective physicalMatching := by
    intro first second heq
    apply orbit.sourceEquiv.symm.injective
    apply hinjective
    apply orbit.targetEquiv.injective
    exact heq
  have hphysicalRelated : forall source, orbit.Related source
      (physicalMatching source) := by
    intro source
    let booleanSource := orbit.sourceEquiv.symm source
    have hrel := hmatching booleanSource
    have := (orbit.related_equiv booleanSource
      (matching booleanSource)).2 hrel
    simpa [physicalMatching, booleanSource] using this
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective orbit.Related).2
    ⟨physicalMatching, hphysicalInjective, hphysicalRelated⟩

end SixVertexDegreeTwoUnitComponentOrbitPresentation





structure SixVertexDegreeTwoUnitComponentOrbitAtlas
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (Source : Type*) [Fintype Source] where
  sourcePhysical : Source ↪
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  Orbit : Type
  SourceOrbit : Orbit -> Type
  TargetOrbit : Orbit -> Type
  sourceOrbitPhysical : forall index, SourceOrbit index ->
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  targetOrbitPhysical : forall index, TargetOrbit index ->
    SixVertexConfigurationPhysicalTarget T middle
  localMatching : forall index, SourceOrbit index ↪ TargetOrbit index
  localMatching_related : forall index source,
    SixVertexDegreeTwoUnitStrandPhysicalRelated
      (sourceOrbitPhysical index source)
      (targetOrbitPhysical index (localMatching index source))
  sourceCover : Source ≃ Σ index, SourceOrbit index
  sourceCover_physical : forall source,
    sourceOrbitPhysical (sourceCover source).1 (sourceCover source).2 =
      sourcePhysical source
  targetEmbedding : (Σ index, TargetOrbit index) ↪
    SixVertexConfigurationPhysicalTarget T middle
  targetEmbedding_physical : forall index target,
    targetEmbedding ⟨index, target⟩ = targetOrbitPhysical index target

namespace SixVertexDegreeTwoUnitComponentOrbitAtlas

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Source : Type*} [Fintype Source]



def Related
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source)
    (source : Source) (target : SixVertexConfigurationPhysicalTarget T middle) :
    Prop :=
  SixVertexDegreeTwoUnitStrandPhysicalRelated
    (atlas.sourcePhysical source) target



noncomputable def matching
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source) :
    Source ↪ SixVertexConfigurationPhysicalTarget T middle :=
  atlas.sourceCover.toEmbedding |>.trans
    ({
      toFun := fun source =>
        ⟨source.1, atlas.localMatching source.1 source.2⟩
      inj' := by
        rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ heq
        have hindex : firstIndex = secondIndex := congrArg Sigma.fst heq
        subst secondIndex
        have hfiber :
            atlas.localMatching firstIndex first =
              atlas.localMatching firstIndex second := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have := (atlas.localMatching firstIndex).injective hfiber
        cases this
        rfl } :
      (Σ index, atlas.SourceOrbit index) ↪
        (Σ index, atlas.TargetOrbit index)) |>.trans
    atlas.targetEmbedding

theorem matching_related
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    atlas.Related source (atlas.matching source) := by
  let covered := atlas.sourceCover source
  have hlocal := atlas.localMatching_related covered.1 covered.2
  unfold Related
  rw [← atlas.sourceCover_physical source]
  change SixVertexDegreeTwoUnitStrandPhysicalRelated
    (atlas.sourceOrbitPhysical covered.1 covered.2)
    (atlas.matching source)
  rw [show atlas.matching source =
      atlas.targetEmbedding
        ⟨covered.1, atlas.localMatching covered.1 covered.2⟩ by rfl,
    atlas.targetEmbedding_physical]
  exact hlocal



theorem hall
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target :
            SixVertexConfigurationPhysicalTarget T middle =>
          ∃ source ∈ sources, atlas.Related source target).card := by
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective atlas.Related).2
    ⟨atlas.matching, atlas.matching.injective, atlas.matching_related⟩

end SixVertexDegreeTwoUnitComponentOrbitAtlas

end

end StatMech.FrontierD
