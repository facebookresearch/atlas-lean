/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.RelativeCyclicGluing

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.RelativeCyclicGluing
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace MathlibExtTest.CategoryTheory.RelativeCyclicGluing

abbrev K := (𝟙_ (Cochains ℚ))
abbrev e : K ⟶ K := 0
abbrev f : K ⟶ K := 𝟙 _
abbrev g : K ⟶ K := 𝟙 _
abbrev h : K ⟶ K := 0
abbrev d := boundaryDifference e f g h
abbrev H := compatibleComplex e f g h
def oneK : K.X 0 := (1 : ℚ)

example : oneK ≠ 0 := by change (1 : ℚ) ≠ 0; norm_num

def exteriorAInjection : K.X 0 ⟶ H.X (-1) :=
  (biprod.inl : K ⟶ K ⊞ K).f 0 ≫
    (CochainComplex.mappingCone.inl (biprod.desc e f)).v 0 (-1) (by omega) ≫
    (biprod.inl : relativeX e f ⟶ relativeX e f ⊞ relativeY g h).f (-1) ≫
    (CochainComplex.mappingCone.inl d).v (-1) (-2) (by omega) ≫
    ((CochainComplex.mappingCone d).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).inv

def compatibilityInjection : K.X 0 ⟶ H.X 0 :=
  (K.shiftFunctorObjXIso 1 (-1) 0 (by omega)).inv ≫
    (CochainComplex.mappingCone.inr d).f (-1) ≫
    ((CochainComplex.mappingCone d).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).inv

lemma exterior_projection : exteriorAInjection ≫ exteriorA e f g h (-1) = 𝟙 (K.X 0) := by
  unfold exteriorAInjection exteriorA projectionX
  dsimp [H, d, compatibleComplex]
  rw [compatibleProjection_f]
  dsimp [CochainComplex.shiftFunctorObjXIso]
  simp only [Category.assoc, Category.id_comp, Category.comp_id]
  rw [CochainComplex.mappingCone.inl_v_fst_v_assoc]
  have hp : (biprod.inl : relativeX e f ⟶ relativeX e f ⊞ relativeY g h).f (-1) ≫
      (biprod.fst : relativeX e f ⊞ relativeY g h ⟶ relativeX e f).f (-1) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inl_fst]
    rfl
  calc
    _ = (biprod.inl : K ⟶ K ⊞ K).f 0 ≫
        (CochainComplex.mappingCone.inl (biprod.desc e f)).v 0 (-1) (by omega) ≫
        𝟙 ((relativeX e f).X (-1)) ≫
        (CochainComplex.mappingCone.fst (biprod.desc e f)).val.v (-1) 0 rfl ≫
        (biprod.fst : K ⊞ K ⟶ K).f 0 := by
      simpa only [Category.assoc] using congrArg
        (fun m => (biprod.inl : K ⟶ K ⊞ K).f 0 ≫
          (CochainComplex.mappingCone.inl (biprod.desc e f)).v 0 (-1) (by omega) ≫ m ≫
          (CochainComplex.mappingCone.fst (biprod.desc e f)).val.v (-1) 0 rfl ≫
          (biprod.fst : K ⊞ K ⟶ K).f 0) hp
    _ = _ := by
      unfold relativeX
      simp only [Category.id_comp]
      rw [CochainComplex.mappingCone.inl_v_fst_v_assoc]
      rw [← HomologicalComplex.comp_f, biprod.inl_fst]
      rfl

lemma compatibility_projection : compatibilityInjection ≫ interiorZ e f g h (𝟙 K) (𝟙 K) 0 = 𝟙 (K.X 0) := by
  unfold compatibilityInjection interiorZ projectionX projectionY compatibilityDegree
  dsimp [H, d, compatibleComplex]
  rw [compatibleProjection_f]
  dsimp [CochainComplex.shiftFunctorObjXIso]
  simp only [Preadditive.comp_add, Category.assoc, Category.id_comp, Category.comp_id,
    CochainComplex.mappingCone.inr_f_fst_v_assoc, zero_comp, zero_add]
  rw [CochainComplex.mappingCone.inr_f_snd_v]
  rfl

/-! A nonzero exterior class survives in the relative output, although the
absolute K target has no degree -1 coefficient. -/
example : exteriorAInjection ≫ gluingDegree e f g h (𝟙 K) (𝟙 K) (-1) ≫
    (CochainComplex.mappingCone.fst (biprod.desc (e ≫ 𝟙 K) (h ≫ 𝟙 K))).val.v (-1) 0 rfl ≫
    (biprod.fst : K ⊞ K ⟶ K).f 0 = 𝟙 (K.X 0) := by
  have he := gluingDegree_exteriorA e f g h (𝟙 K) (𝟙 K) (-1)
  simpa only [Category.assoc, Int.reduceNeg, Int.reduceAdd] using (congrArg (fun m => exteriorAInjection ≫ m) he).trans exterior_projection

/-! The shared B compatibility term survives the actual gluing operation. -/
example : compatibilityInjection ≫ gluingDegree e f g h (𝟙 K) (𝟙 K) 0 ≫
    (CochainComplex.mappingCone.snd (biprod.desc (e ≫ 𝟙 K) (h ≫ 𝟙 K))).v 0 0 rfl = 𝟙 (K.X 0) := by
  have he := gluingDegree_interiorZ e f g h (𝟙 K) (𝟙 K) 0
  simpa only [Category.assoc, Int.reduceNeg, Int.reduceAdd] using (congrArg (fun m => compatibilityInjection ≫ m) he).trans compatibility_projection

abbrev ds := sourceBoundaryDifference e f g h
abbrev sourceH := sourceCompatibleComplex e f g h

def sourceCompatibilityInjection : K.X 0 ⟶ sourceH.X 0 :=
  (K.shiftFunctorObjXIso 1 (-1) 0 (by omega)).inv ≫
    (CochainComplex.mappingCone.inr ds).f (-1) ≫
    ((CochainComplex.mappingCone ds).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).inv

/-! The primary difference convention changes the nonzero B compatibility coefficient by -1. -/
example : sourceCompatibilityInjection ≫ (sourceToCompatibleIso e f g h).hom.f 0 ≫
    compatibilityDegree e f g h 0 = -(𝟙 (K.X 0)) := by
  unfold sourceCompatibilityInjection sourceToCompatibleIso compatibilityDegree
  dsimp [sourceH, ds, sourceCompatibleComplex, compatibleComplex]
  simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain, Cochain.comp_v, Cochain.ofHom_v, negationIso]

def sourceCInjection : K.X 0 ⟶ sourceH.X (-1) :=
  (biprod.inr : K ⟶ K ⊞ K).f 0 ≫
    (CochainComplex.mappingCone.inl (biprod.desc g h)).v 0 (-1) (by omega) ≫
    (biprod.inr : relativeY g h ⟶ relativeX e f ⊞ relativeY g h).f (-1) ≫
    (CochainComplex.mappingCone.inl ds).v (-1) (-2) (by omega) ≫
    ((CochainComplex.mappingCone ds).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).inv

lemma source_C_projection_negative : sourceCInjection ≫ (sourceToCompatibleIso e f g h).hom.f (-1) ≫
    exteriorC e f g h (-1) = -(𝟙 (K.X 0)) := by
  unfold sourceCInjection sourceToCompatibleIso exteriorC projectionY
  dsimp [sourceH, ds, sourceCompatibleComplex, compatibleComplex]
  rw [compatibleProjection_f]
  simp only [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc]
  simp [Cochain.ofHom_v, negationIso, CochainComplex.shiftFunctorObjXIso, Category.assoc]
  have hy : (biprod.inr : relativeY g h ⟶ relativeX e f ⊞ relativeY g h).f (-1) ≫
      (biprod.map (𝟙 (relativeX e f)) (-(𝟙 (relativeY g h)))).f (-1) ≫
      (biprod.snd : relativeX e f ⊞ relativeY g h ⟶ relativeY g h).f (-1) =
      -(𝟙 ((relativeY g h).X (-1))) := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    simp
  calc
    _ = (biprod.inr : K ⟶ K ⊞ K).f 0 ≫
        (CochainComplex.mappingCone.inl (biprod.desc g h)).v 0 (-1) (by omega) ≫
        (-(𝟙 ((relativeY g h).X (-1)))) ≫
        (CochainComplex.mappingCone.fst (biprod.desc g h)).val.v (-1) 0 (by omega) ≫
        (biprod.snd : K ⊞ K ⟶ K).f 0 := by
      simpa only [Category.assoc] using congrArg
        (fun m => (biprod.inr : K ⟶ K ⊞ K).f 0 ≫
          (CochainComplex.mappingCone.inl (biprod.desc g h)).v 0 (-1) (by omega) ≫ m ≫
          (CochainComplex.mappingCone.fst (biprod.desc g h)).val.v (-1) 0 (by omega) ≫
          (biprod.snd : K ⊞ K ⟶ K).f 0) hy
    _ = _ := by
      unfold relativeY
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp]
      rw [CochainComplex.mappingCone.inl_v_fst_v_assoc]
      rw [← HomologicalComplex.comp_f, biprod.inr_snd]
      rfl

/-! The source's nonzero C coefficient has negative exterior C image under the actual χ. -/
example : sourceCInjection ≫ (sourceToCompatibleIso e f g h).hom.f (-1) ≫
    gluingDegree e f g h (𝟙 K) (𝟙 K) (-1) ≫
    (CochainComplex.mappingCone.fst (biprod.desc (e ≫ 𝟙 K) (h ≫ 𝟙 K))).val.v (-1) 0 rfl ≫
    (biprod.snd : K ⊞ K ⟶ K).f 0 = -(𝟙 (K.X 0)) := by
  have he := gluingDegree_exteriorC e f g h (𝟙 K) (𝟙 K) (-1)
  simpa only [Category.assoc, Int.reduceNeg, Int.reduceAdd] using
    (congrArg (fun m => sourceCInjection ≫ (sourceToCompatibleIso e f g h).hom.f (-1) ≫ m) he).trans
      source_C_projection_negative

end MathlibExtTest.CategoryTheory.RelativeCyclicGluing
