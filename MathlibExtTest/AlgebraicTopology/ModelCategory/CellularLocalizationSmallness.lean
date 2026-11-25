/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationSmallness
public import Batteries.Tactic.Lint

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v vD
open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularLocalizationSmallness

namespace CellularLocalizationSmallnessClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)
  {W : C} {γ : Cardinal.{w}}

example (hW : IsCellularCompactAt.{w} d.I W γ) :
    IsUniformlySmallRelativeTo.{w} d.I W := uniformly_small_of_compactAt h hW

example (hW : IsCellularCompact.{w} d.I W) :
    IsUniformlySmallRelativeTo.{w} d.I W := uniformly_small_of_compact h hW

example (i : d.I.toSet) : IsUniformlySmallRelativeTo.{w} d.I i.1.left :=
  uniformly_small_of_compactAt h (domain_compact h i)

example (i : d.I.toSet) : IsUniformlySmallRelativeTo.{w} d.I i.1.right :=
  uniformly_small_of_compactAt h (codomain_compact h i)

example {A B : C} (R : Retract B A) (hA : IsUniformlySmallRelativeTo.{w} d.I A) :
    IsUniformlySmallRelativeTo.{w} d.I B := hA.of_retract R

example (W : C) [IsCofibrant W] : IsUniformlySmallRelativeTo.{w} d.I W :=
  cofibrant_uniformly_small h W

example (j : d.J.toSet) : IsUniformlySmallRelativeTo.{w} d.I j.1.right :=
  J_codomain_uniformly_small h j

example (j : d.J.toSet) : IsUniformlySmallRelativeTo.{w} d.J j.1.left :=
  J_domain_uniformly_small_relative_J h j

example (j : d.J.toSet) : IsUniformlySmallRelativeTo.{w} d.J j.1.right :=
  J_codomain_uniformly_small_relative_J h j

section ActualCofibrationChain

variable (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
  (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
  (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
    cofibrations C (F.map (homOfLE (Order.le_succ a))))
  (s : Cocone F) (hs : IsColimit s)

example (hW : IsCellularCompactAt.{w} d.I W γ) (hγ : γ < μ) :
    IsColimit ((coyoneda.obj (op W)).mapCocone s) :=
  mappedOriginalCofibrationCoconeOfCompact h hW μ hγ F hF s hs

example (hW : IsCellularCompactAt.{w} d.I W γ) (hγ : γ < μ) (f : W ⟶ s.pt) :
    ∃ (a : μ.ord.ToType) (g : W ⟶ F.obj a), g ≫ s.ι.app a = f := by
  let _ : PreservesColimit F (coyoneda.obj (op W)) :=
    preserves_original_cofibration_chain_of_compact h hW μ hγ F hF
  exact exists_hom_of_preservesColimit_coyoneda hs f

example (hW : IsCellularCompactAt.{w} d.I W γ) (hγ : γ < μ)
    {a b : μ.ord.ToType} (f : W ⟶ F.obj a) (g : W ⟶ F.obj b)
    (hfg : f ≫ s.ι.app a = g ≫ s.ι.app b) :
    ∃ (e : μ.ord.ToType) (p : a ⟶ e) (q : b ⟶ e), f ≫ F.map p = g ≫ F.map q := by
  let _ : PreservesColimit F (coyoneda.obj (op W)) :=
    preserves_original_cofibration_chain_of_compact h hW μ hγ F hF
  exact exists_eq_of_preservesColimit_coyoneda hs f g hfg

example (j : d.J.toSet) (hμ : commonSmallBound h < μ) :
    IsColimit ((coyoneda.obj (op j.1.left)).mapCocone s) :=
  mappedJDomainCofibrationCocone h j μ hμ F hF s hs

example (j : d.J.toSet) (hμ : jCodomainSourceBound h j < μ) :
    IsColimit ((coyoneda.obj (op j.1.right)).mapCocone s) :=
  mappedJCodomainCofibrationCocone h j μ hμ F hF s hs

example (hW : IsUniformlySmallRelativeTo.{w} d.I W)
    (hμ : CellularCofibrationTransport.originalSourceBound d hW < μ) :
    IsColimit ((coyoneda.obj (op W)).mapCocone s) :=
  CellularCofibrationTransport.mappedOriginalCofibrationCocone d hW μ hμ F hF s hs

end ActualCofibrationChain

section OriginalCellHistory

variable {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (hX : IsUniformlySmallRelativeTo.{w} d.I X)

example : IsUniformlySmallRelativeTo.{w} d.I Y := cell_endpoint_uniformly_small h hX c

example (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : cellEndpointSourceBound h hX c < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      cofibrations C (F.map (homOfLE (Order.le_succ a))))
    (s : Cocone F) (hs : IsColimit s) :
    IsColimit ((coyoneda.obj (op Y)).mapCocone s) :=
  mappedCellEndpointCofibrationCocone h hX c μ hμ F hF s hs

example (f : X ⟶ Y) (hf : cofibrations C f) :
    IsUniformlySmallRelativeTo.{w} d.I Y := cofibration_codomain_uniformly_small h f hf hX

end OriginalCellHistory

end CellularLocalizationSmallnessClients

namespace CellularCompactnessClosureClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

example {D : Type w} [Category.{vD} D] (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (γ : D → Cardinal.{w}) (hF : ∀ i : D, IsCellularCompactAt.{w} d.I (F.obj i) (γ i)) :
    IsCellularCompactAt.{w} d.I s.pt (Cardinal.sum γ) :=
  colimit_compactAt_bounds h F s hs γ hF

example {D : Type w} [Category.{vD} D] (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (γ : Cardinal.{w}) (hF : ∀ i : D, IsCellularCompactAt.{w} d.I (F.obj i) γ) :
    IsCellularCompactAt.{w} d.I s.pt (γ * Cardinal.mk D) :=
  colimit_compactAt h F s hs γ hF

example {D : Type w} [Category.{vD} D] (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (hF : ∀ i : D, IsCellularCompact.{w} d.I (F.obj i)) :
    IsCellularCompact.{w} d.I s.pt := colimit_compact h F s hs hF

example {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y} (hX : IsInitial X)
    (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) :
    IsCellularCompactAt.{w} d.I Y (commonCompactBound h * Cardinal.mk c.Cells) :=
  cell_complex_compactAt h hX c

example {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y} (hX : IsInitial X)
    (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) :
    IsCellularCompact.{w} d.I Y := cell_complex_compact h hX c

example (Y : C) [IsCofibrant Y] : IsCellularCompact.{w} d.I Y := cofibrant_compact h Y

example (Y : C) [IsCofibrant Y] :
    IsCellularCompactAt.{w} d.I Y (cofibrantCompactBound h Y) := cofibrant_compactAt h Y

example (Y : C) [IsCofibrant Y] : IsUniformlySmallRelativeTo.{w} d.I Y :=
  uniformly_small_of_compactAt h (cofibrant_compactAt h Y)

end CellularCompactnessClosureClients

#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.exists_regular_stage_bound
#print axioms HomotopicalAlgebra.IsCellularCompactAt.exists_stage_of_cell_history
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.relativeCellMaps_le_cofibrations
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.original_chain_mono
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.mappedOriginalHistoriesOfCompact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.preserves_original_chain_of_compact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.uniformly_small_of_compactAt
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.uniformly_small_of_compact
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalLeftClass
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalFactoryCellMap
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalFactoryRetract
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalFactoryCellMap_mem
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalSection
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalSplitDiagram
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalTargetDiagram
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalSourceDiagram
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalTargetContinuous
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalTargetSuccessor
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalInclusion
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalRetraction
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalSplitting
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.mappedCoconeOfSplitting
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.originalSourceBound
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.mappedOriginalCofibrationCocone
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.preservesOriginalCofibrationChain
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.existsOriginalCofibrationStage
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.existsOriginalCofibrationStageEquality
#print axioms HomotopicalAlgebra.CellularCofibrationTransport.uniformOriginalCofibrationChains
#print axioms HomotopicalAlgebra.IsUniformlySmallRelativeTo.of_retract
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.initial_uniformly_small
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.mappedOriginalCofibrationCoconeOfCompact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.preserves_original_cofibration_chain_of_compact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.uniform_cofibration_chains_of_compactAt
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibration_chain_mono
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cellEndpointSourceBound
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.mappedCellEndpointCofibrationCocone
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cell_endpoint_preserves_cofibration_chain
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cell_endpoint_uniformly_small
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibration_codomain_uniformly_small
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibrant_uniformly_small
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibrant_uniform_cofibration_chains
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.J_codomain_uniformly_small
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.relative_J_maps_le_cofibrations
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.original_J_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.mappedJDomainCofibrationCocone
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.jCodomainSourceBound
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.mappedJCodomainCofibrationCocone
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.J_domain_uniformly_small_relative_J
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.J_codomain_uniformly_small_relative_J
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimit_compactAt_bounds
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimit_compactAt
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimit_compact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cell_complex_compactAt
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cell_complex_compact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibrant_compact
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibrantCompactBound
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.cofibrant_compactAt


namespace CellularColimitSmallnessPromotedClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularLocalizationSmallness

section OriginalColimit

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)
  {D : Type w} [Category.{vD} D]
  (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
  (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i))

example (i : D) : CellularCofibrationTransport.originalSourceBound d (hF i) ≤
    colimitSourceBound F hF := colimitSourceBound_component_le F hF i

example : Cardinal.mk D ≤ colimitSourceBound F hF := colimitSourceBound_objects_le F hF

example : IsUniformlySmallRelativeTo.{w} d.I s.pt := colimit_uniformly_small h F s hs hF

example :
    ∃ β : Cardinal.{w},
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType], β < μ →
        ∀ (G : μ.ord.ToType ⥤ C) [G.IsWellOrderContinuous],
          (∀ j : μ.ord.ToType, ¬ IsMax j →
            cofibrations C (G.map (homOfLE (Order.le_succ j)))) →
          PreservesColimit G (coyoneda.obj (op s.pt)) :=
  colimit_uniform_cofibration_chains h F s hs hF

variable (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
  (hμ : colimitSourceBound F hF < μ)
  (G : μ.ord.ToType ⥤ C) [G.IsWellOrderContinuous]
  (hG : ∀ j : μ.ord.ToType, ¬ IsMax j →
    cofibrations C (G.map (homOfLE (Order.le_succ j))))
  (t : Cocone G) (ht : IsColimit t)

example : PreservesColimit G (coyoneda.obj (op s.pt)) :=
  colimit_preserves_cofibration_chain h F s hs hF μ hμ G hG

example : IsColimit ((coyoneda.obj (op s.pt)).mapCocone t) :=
  mappedColimitCofibrationCocone h F s hs hF μ hμ G hG t ht

example (g : s.pt ⟶ t.pt) :
    ∃ (j : μ.ord.ToType) (b : s.pt ⟶ G.obj j), b ≫ t.ι.app j = g := by
  let _ : PreservesColimit G (coyoneda.obj (op s.pt)) :=
    colimit_preserves_cofibration_chain h F s hs hF μ hμ G hG
  exact exists_hom_of_preservesColimit_coyoneda ht g

example {i j : μ.ord.ToType} (a : s.pt ⟶ G.obj i) (b : s.pt ⟶ G.obj j)
    (hab : a ≫ t.ι.app i = b ≫ t.ι.app j) :
    ∃ (e : μ.ord.ToType) (u : i ⟶ e) (v : j ⟶ e), a ≫ G.map u = b ≫ G.map v := by
  let _ : PreservesColimit G (coyoneda.obj (op s.pt)) :=
    colimit_preserves_cofibration_chain h F s hs hF μ hμ G hG
  exact exists_eq_of_preservesColimit_coyoneda ht a b hab

end OriginalColimit

section OriginalNoncofibrantJ

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)
  {D : Type w} [Category.{vD} D] (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
  (j : D → d.J.toSet)

example (hlabels : ∀ i : D, F.obj i = (j i).1.left) :
    IsUniformlySmallRelativeTo.{w} d.I s.pt := by
  apply colimit_uniformly_small h F s hs
  intro i
  rw [hlabels i]
  exact h.J_domains_small (j i)

example (hlabels : ∀ i : D, F.obj i = (j i).1.right) :
    IsUniformlySmallRelativeTo.{w} d.I s.pt := by
  apply colimit_uniformly_small h F s hs
  intro i
  rw [hlabels i]
  exact J_codomain_uniformly_small h (j i)

end OriginalNoncofibrantJ

#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimitSourceBound
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimitSourceBound_component_le
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimitSourceBound_objects_le
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.mappedColimitCofibrationCocone
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimit_preserves_cofibration_chain
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimit_uniformly_small
#print axioms HomotopicalAlgebra.CellularLocalizationSmallness.colimit_uniform_cofibration_chains


end CellularColimitSmallnessPromotedClients

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationSmallness
