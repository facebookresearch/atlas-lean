/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitDegreeCoherence

/-!
# Functorial cycles retractions and homology sections

For an additive functor preserving the left homology construction of a
selected degreewise short complex, the canonical cycles and homology
comparison isomorphisms identify the normalized splitting retractions,
inclusions and sections before and after applying the functor.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]

private lemma mapCyclesIso_inv_iCycles (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) [F.Additive] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [← S.mapCyclesIso_hom_iCycles F, Iso.inv_hom_id_assoc]

private lemma mapHomologyIso_homologyπ (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) [F.Additive] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.leftHomologyData
  have heH := h.mapHomologyIso_eq F
  have heZ := h.mapCyclesIso_eq F
  calc
    _ = (S.map F).homologyπ ≫ ((h.map F).homologyIso.hom ≫ F.map h.homologyIso.inv) := by
      rw [heH]
      rfl
    _ = ((S.map F).homologyπ ≫ (h.map F).homologyIso.hom) ≫ F.map h.homologyIso.inv := by
      exact (Category.assoc _ _ _).symm
    _ = ((h.map F).cyclesIso.hom ≫ F.map h.π) ≫ F.map h.homologyIso.inv := by
      rw [(h.map F).homologyπ_comp_homologyIso_hom]
      rfl
    _ = (h.map F).cyclesIso.hom ≫ F.map (h.π ≫ h.homologyIso.inv) := by
      rw [Functor.map_comp]
      exact Category.assoc _ _ _
    _ = (h.map F).cyclesIso.hom ≫ F.map (h.cyclesIso.inv ≫ S.homologyπ) := by
      rw [h.π_comp_homologyIso_inv]
    _ = ((h.map F).cyclesIso.hom ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ := by
      rw [Functor.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
      rw [heZ]
      rfl

variable {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

local instance (F : C ⥤ D) [F.Additive] (i : ι)
    [((F.mapHomologicalComplex c).obj K).HasHomology i] :
    ((K.sc i).map F).HasHomology := by
  change ((F.mapHomologicalComplex c).obj K).HasHomology i
  infer_instance

/--
Let C,D be preadditive categories, K a c-complex with splitting s, and F:C⥤D additive. Assume
K and F(K) have homology at i and F preserves left homology of Sᵢ=(K_prev(i)→Kᵢ→K_next(i)).
Let α_Z:Zᵢ(FK)≅F(ZᵢK) and α_H:Hᵢ(FK)≅F(HᵢK) be the canonical comparisons. For the normalized
cycles retraction rᵢ:Kᵢ→ZᵢK, F(rᵢ)≫α_Z.inv equals the cycles retraction of s.map F.
-/
@[reassoc]
lemma cyclesRetraction_map (s : Splitting K) (F : C ⥤ D) [F.Additive] (i : ι)
    [K.HasHomology i] [((F.mapHomologicalComplex c).obj K).HasHomology i]
    [F.PreservesLeftHomologyOf (K.sc i)] :
    F.map (s.cyclesRetraction i) ≫ ((K.sc i).mapCyclesIso F).inv =
      (s.map F).cyclesRetraction i := by
  apply (cancel_mono (((F.mapHomologicalComplex c).obj K).iCycles i)).1
  have he : ((K.sc i).mapCyclesIso F).inv ≫
      ((F.mapHomologicalComplex c).obj K).iCycles i = F.map (K.iCycles i) :=
    mapCyclesIso_inv_iCycles (K.sc i) F
  calc
    _ = F.map (s.cyclesRetraction i) ≫
        (((K.sc i).mapCyclesIso F).inv ≫ ((F.mapHomologicalComplex c).obj K).iCycles i) :=
      Category.assoc _ _ _
    _ = F.map (s.cyclesRetraction i) ≫ F.map (K.iCycles i) :=
      congrArg (fun f => F.map (s.cyclesRetraction i) ≫ f) he
    _ = F.map (s.cyclesRetraction i ≫ K.iCycles i) := (F.map_comp _ _).symm
    _ = F.map (𝟙 (K.X i) - dNext i s.normalize.hom) :=
      congrArg F.map (s.cyclesRetraction_iCycles i)
    _ = 𝟙 (((F.mapHomologicalComplex c).obj K).X i) - dNext i (s.map F).normalize.hom := by
      simp only [Functor.map_sub, F.map_id, map_normalize, map_dNext_hom]
      rfl
    _ = (s.map F).cyclesRetraction i ≫ ((F.mapHomologicalComplex c).obj K).iCycles i :=
      ((s.map F).cyclesRetraction_iCycles i).symm

/--
Let C,D be preadditive categories, K a c-complex with splitting s, and F:C⥤D additive. Assume
K and F(K) have homology at i and F preserves left homology of Sᵢ=(K_prev(i)→Kᵢ→K_next(i)).
Let α_Z:Zᵢ(FK)≅F(ZᵢK) and α_H:Hᵢ(FK)≅F(HᵢK) be the canonical comparisons. For the normalized
homology inclusion ℓᵢ:HᵢK→Kᵢ, α_H.inv≫ℓᵢ(FK)=F(ℓᵢ), where the mapped inclusion is constructed
from s.map F.
-/
@[reassoc]
lemma homologyInclusionComponent_map (s : Splitting K) (F : C ⥤ D) [F.Additive] (i : ι)
    [K.HasHomology i] [((F.mapHomologicalComplex c).obj K).HasHomology i]
    [F.PreservesLeftHomologyOf (K.sc i)] :
    ((K.sc i).mapHomologyIso F).inv ≫ (s.map F).homologyInclusionComponent i =
      F.map (s.homologyInclusionComponent i) := by
  let Z : (K.sc i).cycles ⟶ K.X i := K.iCycles i
  let π : (K.sc i).cycles ⟶ (K.sc i).homology := K.homologyπ i
  let I : (K.sc i).homology ⟶ K.X i := s.homologyInclusionComponent i
  let mI : ((K.sc i).map F).homology ⟶ F.obj (K.X i) := (s.map F).homologyInclusionComponent i
  let mπ : ((K.sc i).map F).cycles ⟶ ((K.sc i).map F).homology :=
    ((F.mapHomologicalComplex c).obj K).homologyπ i
  let mZ : ((K.sc i).map F).cycles ⟶ F.obj (K.X i) :=
    ((F.mapHomologicalComplex c).obj K).iCycles i
  let p : K.X i ⟶ K.X i := 𝟙 (K.X i) - prevD i s.normalize.hom
  let mp : F.obj (K.X i) ⟶ F.obj (K.X i) := prevD i (s.map F).normalize.hom
  have hmp : mp = F.map (prevD i s.normalize.hom) := by
    dsimp only [mp]
    rw [map_normalize]
    exact s.normalize.map_prevD_hom F i
  have hp : F.map p = 𝟙 (F.obj (K.X i)) - mp := by
    rw [hmp]
    dsimp only [p]
    simp only [Functor.map_sub, F.map_id]
  have hI : mπ ≫ mI = mZ ≫ (𝟙 (F.obj (K.X i)) - mp) :=
    (s.map F).homologyπ_homologyInclusionComponent i
  have hZ : ((K.sc i).mapCyclesIso F).hom ≫ F.map Z = mZ :=
    (K.sc i).mapCyclesIso_hom_iCycles F
  have hH : mπ ≫ ((K.sc i).mapHomologyIso F).hom =
      ((K.sc i).mapCyclesIso F).hom ≫ F.map π :=
    mapHomologyIso_homologyπ (K.sc i) F
  letI : Epi mπ := by
    change Epi (((F.mapHomologicalComplex c).obj K).homologyπ i)
    infer_instance
  change ((K.sc i).mapHomologyIso F).inv ≫ mI = F.map I
  apply (cancel_epi (mπ ≫ ((K.sc i).mapHomologyIso F).hom)).1
  calc
    _ = mπ ≫ mI := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = mZ ≫ F.map p := hI.trans (congrArg (fun f => mZ ≫ f) hp.symm)
    _ = (((K.sc i).mapCyclesIso F).hom ≫ F.map Z) ≫ F.map p :=
      congrArg (fun f => f ≫ F.map p) hZ.symm
    _ = ((K.sc i).mapCyclesIso F).hom ≫ F.map (Z ≫ p) := by
      rw [Functor.map_comp]
      exact Category.assoc _ _ _
    _ = ((K.sc i).mapCyclesIso F).hom ≫ F.map (π ≫ I) :=
      congrArg (fun f => ((K.sc i).mapCyclesIso F).hom ≫ F.map f)
        (s.homologyπ_homologyInclusionComponent i).symm
    _ = (((K.sc i).mapCyclesIso F).hom ≫ F.map π) ≫
        F.map I := by
      rw [Functor.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = (mπ ≫ ((K.sc i).mapHomologyIso F).hom) ≫ F.map I :=
      congrArg (fun f => f ≫ F.map I) hH.symm

/--
Let C,D be preadditive categories, K a c-complex with splitting s, and F:C⥤D additive. Assume
K and F(K) have homology at i and F preserves left homology of Sᵢ=(K_prev(i)→Kᵢ→K_next(i)).
Let α_Z:Zᵢ(FK)≅F(ZᵢK) and α_H:Hᵢ(FK)≅F(HᵢK) be the canonical comparisons. For the
homology-to-cycles section tᵢ:HᵢK→ZᵢK, F(tᵢ)≫α_Z.inv=α_H.inv≫tᵢ(FK).
-/
@[reassoc]
lemma homologyCycleSection_map (s : Splitting K) (F : C ⥤ D) [F.Additive] (i : ι)
    [K.HasHomology i] [((F.mapHomologicalComplex c).obj K).HasHomology i]
    [F.PreservesLeftHomologyOf (K.sc i)] :
    F.map (s.homologyCycleSection i) ≫ ((K.sc i).mapCyclesIso F).inv =
      ((K.sc i).mapHomologyIso F).inv ≫ (s.map F).homologyCycleSection i := by
  let I : (K.sc i).homology ⟶ K.X i := s.homologyInclusionComponent i
  let R : K.X i ⟶ (K.sc i).cycles := s.cyclesRetraction i
  let mI : ((K.sc i).map F).homology ⟶ F.obj (K.X i) := (s.map F).homologyInclusionComponent i
  let mR : F.obj (K.X i) ⟶ ((K.sc i).map F).cycles := (s.map F).cyclesRetraction i
  have hR : F.map R ≫ ((K.sc i).mapCyclesIso F).inv = mR := s.cyclesRetraction_map F i
  have hI : ((K.sc i).mapHomologyIso F).inv ≫ mI = F.map I :=
    s.homologyInclusionComponent_map F i
  change F.map (I ≫ R) ≫ ((K.sc i).mapCyclesIso F).inv =
    ((K.sc i).mapHomologyIso F).inv ≫ (mI ≫ mR)
  rw [Functor.map_comp]
  calc
    _ = F.map I ≫ (F.map R ≫ ((K.sc i).mapCyclesIso F).inv) := Category.assoc _ _ _
    _ = F.map I ≫ mR := congrArg (fun f => F.map I ≫ f) hR
    _ = (((K.sc i).mapHomologyIso F).inv ≫ mI) ≫ mR := congrArg (fun f => f ≫ mR) hI.symm
    _ = _ := Category.assoc _ _ _

end HomologicalComplex.Splitting
