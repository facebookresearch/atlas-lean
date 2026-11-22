/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalReplacement
public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentBrownHo
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalModel
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy

/-!
# Actual original K lifting and arbitrary-source K-replacement maps

Every strict relative native map equality lifts through SAME original J
path object into SAME original K-local target. Its two projections agree
under the actual native level-Ho projection without source cofibrancy.
Thus original K-left maps between original K-local objects are level TC,
and the original K unit on ANY original Omega input is level weak.
The same original K unit/terminal lifts construct BOTH complete inverse
functions for L(f) when f is ANY K-left map, arbitrary original source.
Both original K-unit idempotence maps are level weak and agree ONLY after
original level-Ho projection, with whole native input transformations.
Original I/J/K/cardinal/B/Z/i/p/fac/model/source/unit choices are retained.
General K-left pi-star/Omega-test recognition and actual stable model/FS/
properness remain REQUIRED OPEN; no desired recognition dictionary enters.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC uD vD
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

private theorem property_iff_of_natural_weak_maps
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (P : MorphismProperty D) [P.HasTwoOutOfThreeProperty]
    {F G : C ⥤ D} (η : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (hF : P (F.map f)) (hG : P (G.map f)) : P (η.app X) ↔ P (η.app Y) := by
  constructor
  · intro hX
    have h := P.comp_mem _ _ hX hG
    rw [← η.naturality f] at h
    exact P.of_precomp _ _ hF h
  · intro hY
    have h := P.comp_mem _ _ hF hY
    rw [η.naturality f] at h
    exact P.of_postcomp _ _ hG h

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

section ActualPath
variable {C : Type uC} [Category.{vC} C] [ModelCategory C] {Z : C}

/-- BOTH original path projections agree in Ho from the same actual weak section. -/
theorem originalPathProjections_Ho_eq (P : PathObject Z) :
    (toHomotopyCategory C).map P.p₀ = (toHomotopyCategory C).map P.p₁ := by
  let H := toHomotopyCategory C
  let _ : IsIso (H.map P.ι) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map P.ι).mp
      (HomotopicalAlgebra.mem_weakEquivalences P.ι)
  apply (cancel_epi (H.map P.ι)).mp
  change H.map P.ι ≫ H.map P.p₀ = H.map P.ι ≫ H.map P.p₁
  rw [← H.map_comp, ← H.map_comp, P.ι_p₀, P.ι_p₁]

/-- An actual original path witness gives the exact two original projected map functions. -/
theorem originalPathWitness_Ho_eq (P : PathObject Z) {A : C}
    (a : A ⟶ P.P) (g h : A ⟶ Z) (hg : a ≫ P.p₀ = g) (hh : a ≫ P.p₁ = h) :
    (toHomotopyCategory C).map g = (toHomotopyCategory C).map h := by
  let witness : P.RightHomotopy g h := { h := a, h₀ := hg, h₁ := hh }
  exact ((RightHomotopyRel.factorsThroughLocalization C) witness.rightHomotopyRel).map_eq
    (toHomotopyCategory C)

end ActualPath

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open PointedCGWH.EnrichedFunctorMapping
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

/-- The actual original terminal square retains the provided source arrow and native map. -/
theorem originalKTerminalSquare
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (E : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (g : X ⟶ E) :
    CommSq g i (toZero E) (toZero Y) := ⟨zeroDiagramIsTerminal.hom_ext _ _⟩

/-- Original K lifting constructs the actual extension along every original K-left arrow. -/
def originalKLeftExtension
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (E : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hE : (generators s).rlp (toZero E)) (g : X ⟶ E) : Y ⟶ E := by
  let _ : HasLiftingProperty i (toZero E) := hi _ hE
  exact (originalKTerminalSquare i E g).lift

/-- The full actual extension retains precisely the original source composite. -/
theorem originalKLeftExtension_section
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (E : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hE : (generators s).rlp (toZero E)) (g : X ⟶ E) :
    i ≫ (originalKLeftExtension s) i hi E hE g = g := by
  let _ : HasLiftingProperty i (toZero E) := hi _ hE
  exact (originalKTerminalSquare i E g).fac_left

/-- The SAME original terminal lift constructs the actual local source inverse. -/
def originalKLeftLocalInverse
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (hX : (generators s).rlp (toZero X)) : Y ⟶ X :=
  (originalKLeftExtension s) i hi X hX (𝟙 X)

/-- Its first original inverse equation is STRICT on the actual native maps, every source. -/
theorem originalKLeftLocalInverse_section
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (hX : (generators s).rlp (toZero X)) :
    i ≫ (originalKLeftLocalInverse s) i hi hX = 𝟙 X :=
  (originalKLeftExtension_section s) i hi X hX (𝟙 X)




variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The two original stabilization mapping-source tests agree across every level weak map. -/
theorem originalKMappingSourceWeak_iff_of_levelWeak (l : L)
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre (cylinderSource s l)
      X) ↔
      weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre (cylinderSource s
        l) Y) := by
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).mpr hf
  let _ : IsFibrant X := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant X
  let _ : IsFibrant Y := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant Y
  let A := (Arrow.mk
    (stabilization s l)).left
  let C := cylinder s l
  let _ : IsCofibrant A := stabilization_source_cofibrant s l
  let _ : IsCofibrant C := cylinder_cofibrant s l
  let W := weakEquivalences PointedCGWH.{u, v}
  let _ : (tensorMappingAdjunction C).IsQuillenAdjunction :=
    PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen C
  let _ : (tensorMappingAdjunction A).IsQuillenAdjunction :=
    PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen A
  have hC : W (WeightedEndVariance.post C f) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
        (adj := tensorMappingAdjunction C) f)
  have hA : W (WeightedEndVariance.post A f) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
        (adj := tensorMappingAdjunction A) f)
  exact property_iff_of_natural_weak_maps W
    (WeightedEndVariance.bifunctor.map (cylinderSource s l).op) f hC hA

/-- Original K-local terminal lifting is invariant under every native level weak map. -/
theorem originalKLocal_iff_of_levelWeak
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    (generators s).rlp (toZero X) ↔ (generators s).rlp (toZero Y) := by
  let _ : IsFibrant X := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant X
  let _ : IsFibrant Y := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant Y
  constructor
  · intro hX
    apply (lifting_iff s (toZero Y)).mpr
    refine ⟨?_, fun l => ?_⟩
    · exact (HomotopicalAlgebra.fibration_iff _).mp
        ((isFibrant_iff_of_isTerminal (toZero Y) zeroDiagramIsTerminal).mp
          (inferInstance : IsFibrant Y))
    · have hW := ((originalKMappingSourceWeak_iff_of_levelWeak s) l f hf).mp
        (mappingSource_trivial_of_local s l X hX).2
      exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
        (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (cylinderSource s l) Y)).mpr
          ⟨mapSource_fibration (cylinderSource s l)
            ((HomotopicalAlgebra.cofibration_iff _).mp (cylinderSource_cofibration s l)) Y, hW⟩
  · intro hY
    apply (lifting_iff s (toZero X)).mpr
    refine ⟨?_, fun l => ?_⟩
    · exact (HomotopicalAlgebra.fibration_iff _).mp
        ((isFibrant_iff_of_isTerminal (toZero X) zeroDiagramIsTerminal).mp
          (inferInstance : IsFibrant X))
    · have hW := ((originalKMappingSourceWeak_iff_of_levelWeak s) l f hf).mpr
        (mappingSource_trivial_of_local s l Y hY).2
      exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
        (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (cylinderSource s l) X)).mpr
          ⟨mapSource_fibration (cylinderSource s l)
            ((HomotopicalAlgebra.cofibration_iff _).mp (cylinderSource_cofibration s l)) X, hW⟩

/-- Actual native Ω spectra are invariant under level weakness through their original K tests. -/
theorem originalOmega_iff_of_levelWeak
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    IsOmega s X ↔ IsOmega s Y :=
  (lifting_toZero_iff_isOmega s X).symm.trans
    (((originalKLocal_iff_of_levelWeak s) f hf).trans (lifting_toZero_iff_isOmega s Y))

/-- Actual K-left relative agreement gives Ho equality at every original local target. -/
theorem originalKLeft_relative_Ho_eq
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) (g h : Y ⟶ Z) (hgh : i ≫ g = i ≫ h) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map g =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map h := by
  let P := HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject (B := B) Z
  let _ : P.IsVeryGood :=
    HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject_isVeryGood Z
  let _ : HasLiftingProperty i P.p := hi _ ((goodPath_projection_mem_right s) Z hZ P)
  have sq : CommSq ((i ≫ g) ≫ P.ι) i P.p (prod.lift g h) :=
    { w := by
        apply prod.hom_ext
        · simp only [Category.assoc, P.p_fst, P.ι_p₀, Category.comp_id, prod.lift_fst]
        · simpa only [Category.assoc, P.p_snd, P.ι_p₁, Category.comp_id, prod.lift_snd] using hgh }
  have hg : sq.lift ≫ P.p₀ = g := by
    simpa only [Category.assoc, P.p_fst, prod.lift_fst] using
      congrArg (fun q => q ≫ prod.fst) sq.fac_right
  have hh : sq.lift ≫ P.p₁ = h := by
    simpa only [Category.assoc, P.p_snd, prod.lift_snd] using
      congrArg (fun q => q ≫ prod.snd) sq.fac_right
  exact originalPathWitness_Ho_eq P sq.lift g h hg hh

/-- EVERY original target input preserves the same actual extension after Ho projection. -/
theorem originalKLeftExtension_target_Ho
    {X Y E E' : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (hE : (generators s).rlp (toZero E))
    (hE' : (generators s).rlp (toZero E')) (f : E ⟶ E') (g : X ⟶ E) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((originalKLeftExtension s) i hi E hE g ≫ f) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((originalKLeftExtension s) i hi E' hE' (g ≫ f)) := by
  apply (originalKLeft_relative_Ho_eq s) i hi E' hE'
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ f) ((originalKLeftExtension_section s) i hi E hE g)).trans
      ((originalKLeftExtension_section s) i hi E' hE' (g ≫ f)).symm)

/-- EVERY original Arrow input preserves the full extension after SAME native Ho projection. -/
theorem originalKLeftExtension_source_Ho
    {X Y X' Y' E : (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (i : X ⟶ Y) (j : X' ⟶ Y') (hi : (generators s).rlp.llp i) (hj : (generators s).rlp.llp j)
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : j ≫ b = a ≫ i)
    (hE : (generators s).rlp (toZero E)) (g : X ⟶ E) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (b ≫ (originalKLeftExtension s) i hi E hE g) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((originalKLeftExtension s) j hj E hE (a ≫ g)) := by
  apply (originalKLeft_relative_Ho_eq s) j hj E hE
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (originalKLeftExtension s) i hi E hE g) w).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => a ≫ t) ((originalKLeftExtension_section s) i hi E hE g)).trans
          ((originalKLeftExtension_section s) j hj E hE (a ≫ g)).symm)))

/-- Arbitrary-source K-left maps between SAME local objects have the complete actual Ho Iso. -/
def originalKLeftLocalHoIso
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (hX : (generators s).rlp (toZero X))
    (hY : (generators s).rlp (toZero Y)) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ≅
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y where
  hom := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map i
  inv := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((originalKLeftLocalInverse s) i hi hX)
  hom_inv_id := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    exact (H.map_comp _ _).symm.trans
      ((H.congr_map ((originalKLeftLocalInverse_section s) i hi hX)).trans (H.map_id X))
  inv_hom_id := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    let g := (originalKLeftLocalInverse s) i hi hX
    have hfg : i ≫ g = 𝟙 X := (originalKLeftLocalInverse_section s) i hi hX
    have hAgree : i ≫ (g ≫ i) = i ≫ 𝟙 Y := by
      rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
    exact (H.map_comp _ _).symm.trans
      (((originalKLeft_relative_Ho_eq s) i hi Y hY (g ≫ i) (𝟙 Y) hAgree).trans (H.map_id Y))

/-- Every actual original K-left arrow between local objects is level weak, no source cofibrancy. -/
theorem originalKLeft_betweenLocal_modelWeak
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (hX : (generators s).rlp (toZero X))
    (hY : (generators s).rlp (toZero Y)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) i :=
  (weakEquivalence_iff_isIso_toHomotopyCategory_map i).mpr
    ((originalKLeftLocalHoIso s) i hi hX hY).isIso_hom

/-- The same arbitrary-source local K-left arrow is an actual original level trivial cofibration. -/
theorem originalKLeft_betweenLocal_trivialCofibration
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hi : (generators s).rlp.llp i) (hX : (generators s).rlp (toZero X))
    (hY : (generators s).rlp (toZero Y)) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i :=
  ⟨(left_le_cofibrations s) i hi, (originalKLeft_betweenLocal_modelWeak s) i hi hX hY⟩

/-- The entire original level-TC class is retained in the exact original K-left class. -/
theorem originalLevelTrivialCofibrations_le_KLeft :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ≤ (generators s).rlp.llp := by
  intro X Y i hi
  have hi' : (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).llp i := by
    rwa [fibrations_llp]
  intro A C p hp
  exact hi' p (((lifting_iff s) p).mp hp).1

/-- BOTH actual K-left/level-TC directions agree on arbitrary-source native local arrows. -/
theorem originalKLeft_iff_levelTC_betweenLocal
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (i : X ⟶ Y)
    (hX : (generators s).rlp (toZero X)) (hY : (generators s).rlp (toZero Y)) :
    (generators s).rlp.llp i ↔ trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i :=
  ⟨fun hi => (originalKLeft_betweenLocal_trivialCofibration s) i hi hX hY,
    fun hi => (originalLevelTrivialCofibrations_le_KLeft s) i hi⟩

/-- Every original Omega input has its SAME original K-unit level weak. -/
theorem originalKUnitOnOmega_modelWeak
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hX : IsOmega s X) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacementUnit s).app X) :=
  (originalKLeft_betweenLocal_modelWeak s) _ ((localReplacementUnit_mem_left s) X)
    ((lifting_toZero_iff_isOmega s X).mpr hX) ((localReplacement_isLocal s) X)

/-- Every SAME original K-unit at its actual original local output is level weak. -/
theorem originalKUnitAtLocalReplacement_modelWeak (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((localReplacementUnit s).app ((localReplacement s).obj X)) :=
  (originalKUnitOnOmega_modelWeak s) _
    (((lifting_toZero_iff_isOmega s) _).mp ((localReplacement_isLocal s) X))

/-- SAME original K replacement preserves and reflects native level W on original Omega arrows. -/
theorem originalKReplacement_omegaMap_modelWeak_iff
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hX : IsOmega s X) (hY : IsOmega s Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacement s).map f) ↔
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f := by
  let W := weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
  have huX := (originalKUnitOnOmega_modelWeak s) X hX
  have huY := (originalKUnitOnOmega_modelWeak s) Y hY
  have hn := (localReplacementUnit_naturality s) f
  constructor
  · intro hf
    have h := W.comp_mem ((localReplacementUnit s).app X) ((localReplacement s).map f) huX hf
    rw [hn] at h
    exact W.of_postcomp f ((localReplacementUnit s).app Y) huY h
  · intro hf
    have h := W.comp_mem f ((localReplacementUnit s).app Y) hf huY
    rw [← hn] at h
    exact W.of_precomp ((localReplacementUnit s).app X) ((localReplacement s).map f) huX h

/-- BOTH original terminal/unit lifts construct the actual inverse of L(f) in level Ho. -/
def originalKReplacementInverse
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) : (localReplacement s).obj Y ⟶ (localReplacement s).obj X :=
  (originalKLeftExtension s) ((localReplacementUnit s).app Y) ((localReplacementUnit_mem_left s) Y)
    ((localReplacement s).obj X) ((localReplacement_isLocal s) X)
    ((originalKLeftExtension s) f hf ((localReplacement s).obj X) ((localReplacement_isLocal s) X)
      ((localReplacementUnit s).app X))

/-- The first chosen inverse factor retains the actual original K unit on Y. -/
theorem originalKReplacementInverse_unit_section
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) :
    (localReplacementUnit s).app Y ≫ (originalKReplacementInverse s) f hf =
      (originalKLeftExtension s) f hf ((localReplacement s).obj X) ((localReplacement_isLocal s) X)
        ((localReplacementUnit s).app X) :=
  (originalKLeftExtension_section s) ((localReplacementUnit s).app Y)
    ((localReplacementUnit_mem_left s) Y)
    ((localReplacement s).obj X) ((localReplacement_isLocal s) X) _

/-- BOTH chosen factors retain the exact original f and original unit on X. -/
theorem originalKReplacementInverse_full_section
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) :
    (f ≫ (localReplacementUnit s).app Y) ≫ (originalKReplacementInverse s) f hf =
      (localReplacementUnit s).app X :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => f ≫ t) ((originalKReplacementInverse_unit_section s) f hf)).trans
      ((originalKLeftExtension_section s) f hf _ ((localReplacement_isLocal s) X) _))

/-- SAME original L(f) is invertible in Ho for EVERY K-left f and arbitrary original source. -/
def originalKReplacementMapHoIso
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ≅
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj Y) where
  hom := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((localReplacement s).map f)
  inv := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((originalKReplacementInverse s) f hf)
  hom_inv_id := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    let g := (originalKReplacementInverse s) f hf
    have hn := (localReplacementUnit_naturality s) f
    have hsec := (originalKReplacementInverse_full_section s) f hf
    have ha : (localReplacementUnit s).app X ≫ ((localReplacement s).map f ≫ g) =
        (localReplacementUnit s).app X ≫ 𝟙 ((localReplacement s).obj X) := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ g) hn).trans
          (hsec.trans (Category.comp_id _).symm))
    exact (H.map_comp _ _).symm.trans
      (((originalKLeft_relative_Ho_eq s) _ ((localReplacementUnit_mem_left s) X) _
        ((localReplacement_isLocal s) X) _ _ ha).trans (H.map_id _))
  inv_hom_id := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    let g := (originalKReplacementInverse s) f hf
    have hn := (localReplacementUnit_naturality s) f
    have hsec := (originalKReplacementInverse_full_section s) f hf
    have hi : (generators s).rlp.llp (f ≫ (localReplacementUnit s).app Y) :=
      (generators s).rlp.llp.comp_mem f _ hf ((localReplacementUnit_mem_left s) Y)
    have ha : (f ≫ (localReplacementUnit s).app Y) ≫ (g ≫ (localReplacement s).map f) =
        (f ≫ (localReplacementUnit s).app Y) ≫ 𝟙 ((localReplacement s).obj Y) := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ (localReplacement s).map f) hsec).trans
          (hn.trans (Category.comp_id _).symm))
    exact (H.map_comp _ _).symm.trans
      (((originalKLeft_relative_Ho_eq s) _ hi _ ((localReplacement_isLocal s) Y) _ _ ha).trans
        (H.map_id _))

/-- EVERY original K-left arrow is sent by SAME original L to level W, without source cofibrancy. -/
theorem originalKReplacementMap_modelWeak_of_KLeft
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacement s).map f) :=
  (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mpr
    ((originalKReplacementMapHoIso s) f hf).isIso_hom

/-- The original L of its SAME original unit is level weak at EVERY original input. -/
theorem originalKReplacementMapUnit_modelWeak (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((localReplacement s).map ((localReplacementUnit s).app X)) :=
  (originalKReplacementMap_modelWeak_of_KLeft s) _ ((localReplacementUnit_mem_left s) X)

/-- SAME original K-unit maps agree only AFTER original level-Ho projection, every input. -/
theorem originalKWeakIdempotence_projected (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacement s).map ((localReplacementUnit s).app X)) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app ((localReplacement s).obj X)) :=
  (originalKLeft_relative_Ho_eq s) _ ((localReplacementUnit_mem_left s) X) _
    ((localReplacement_isLocal s) ((localReplacement s).obj X)) _ _
    ((localReplacementUnit_naturality s) ((localReplacementUnit s).app X))

/-- The actual K-detected class uses SAME original L and SAME caller-B level model. -/
def originalKDetectedWeakEquivalences :
    MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)).inverseImage (localReplacement s)

/-- EVERY original arbitrary-source K-left arrow belongs to that SAME actual original detector. -/
theorem originalKLeft_le_originalKDetectedWeak :
    (generators s).rlp.llp ≤ (originalKDetectedWeakEquivalences.{u, v} s) :=
  fun _ _ f hf => (originalKReplacementMap_modelWeak_of_KLeft s) f hf

/-- First whole original projected weak-idempotence function is unit at L. -/
def originalKUnitAtLProjected :
    (localReplacement.{u, v} s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶
      (localReplacement s) ⋙ (localReplacement s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  app X := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((localReplacementUnit s).app ((localReplacement s).obj X))
  naturality _ _ f := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    exact (H.map_comp _ _).symm.trans
      ((H.congr_map ((localReplacementUnit_naturality s) ((localReplacement s).map f)).symm).trans
        (H.map_comp _ _))

/-- Second whole original projected weak-idempotence function is L of original unit. -/
def originalKLMapUnitProjected :
    (localReplacement.{u, v} s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶
      (localReplacement s) ⋙ (localReplacement s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  app X := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((localReplacement s).map ((localReplacementUnit s).app X))
  naturality _ _ f := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    have hn := ((localReplacement s).map_comp _ _).symm.trans
      (((localReplacement s).congr_map ((localReplacementUnit_naturality s) f).symm).trans
        ((localReplacement s).map_comp _ _))
    exact (H.map_comp _ _).symm.trans ((H.congr_map hn).trans (H.map_comp _ _))

/-- The ENTIRE SAME original projected K-unit transformations agree at every original input. -/
theorem originalKProjectedWeakIdempotenceTransformations_eq :
    (originalKLMapUnitProjected.{u, v} s) = (originalKUnitAtLProjected s) := by
  apply NatTrans.ext
  funext X
  exact (originalKWeakIdempotence_projected s) X

/-- Both original projected K-unit functions are ACTUAL Isos on every original input. -/
theorem originalKProjectedUnits_isIso (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsIso ((originalKUnitAtLProjected s).app X) ∧ IsIso ((originalKLMapUnitProjected s).app X) :=
  ⟨(weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      ((originalKUnitAtLocalReplacement_modelWeak s) X),
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      ((originalKReplacementMapUnit_modelWeak s) X)⟩

/-- The COMPLETE SAME original projected unit-at-L transformation has its actual NatIso value. -/
def originalKUnitAtLProjectedNatIso :
    (localReplacement.{u, v} s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
      (localReplacement s) ⋙ (localReplacement s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  let _ : IsIso (originalKUnitAtLProjected.{u, v} s) :=
    (NatTrans.isIso_iff_isIso_app _).mpr (fun X => ((originalKProjectedUnits_isIso s) X).1)
  exact asIso (originalKUnitAtLProjected s)

/-- The full original NatIso hom is exactly the actual original projected unit transformation. -/
theorem originalKUnitAtLProjectedNatIso_hom :
    (originalKUnitAtLProjectedNatIso.{u, v} s).hom = (originalKUnitAtLProjected s) := rfl

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
