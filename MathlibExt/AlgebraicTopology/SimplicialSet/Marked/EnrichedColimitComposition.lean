/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitIdentity

/-!
# Full composition of original marked colimit Hom actions

The proof uses whole source-injection detection, original middle-map
naturality and the original target injection. Both entire marked prisms
and their common parameter are retained. The resulting composition
law uses the actual enriched source and its genuine marked colimits.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits MonoidalCategory

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)

/-- Original enriched composition descends to the whole marked colimit Hom maps. -/
theorem fullMap_comp (x y z : C) [HasColimit (evaluated K x)]
    [HasColimit (evaluated K y)] [HasColimit (evaluated K z)] :
    eComp SSet.{u} x y z ≫ maxCurry (action K x z) =
      (maxCurry (action K x y) ⊗ₘ maxCurry (action K y z)) ≫
        maxMappingCompose (colimit (evaluated K x)) (colimit (evaluated K y)) (colimit (evaluated K z)) := by
  apply sourceMap_hom_ext K x ((x ⟶[SSet.{u}] y) ⊗ (y ⟶[SSet.{u}] z)) (colimit (evaluated K z))
  intro j
  let A := (K.obj j).obj x
  let B := (K.obj j).obj y
  let D := (K.obj j).obj z
  let L := colimit (evaluated K x)
  let M := colimit (evaluated K y)
  let N := colimit (evaluated K z)
  let p : A ⟶ L := colimit.ι (evaluated K x) j
  let q : B ⟶ M := colimit.ι (evaluated K y) j
  let r : D ⟶ N := colimit.ι (evaluated K z) j
  let f : (x ⟶[SSet.{u}] y) ⟶ mappingComplex .maximal A B := (K.obj j).map x y
  let g : (y ⟶[SSet.{u}] z) ⟶ mappingComplex .maximal B D := (K.obj j).map y z
  let h : (x ⟶[SSet.{u}] z) ⟶ mappingComplex .maximal A D := (K.obj j).map x z
  let a := maxCurry (action K x y)
  let b := maxCurry (action K y z)
  let c := maxCurry (action K x z)
  have hp : a ≫ mappingComplexPre .maximal p M = f ≫ mappingComplexPost .maximal A q :=
    (injection_fullMap K x y j).symm
  have hq : b ≫ mappingComplexPre .maximal q N = g ≫ mappingComplexPost .maximal B r :=
    (injection_fullMap K y z j).symm
  have hr : h ≫ mappingComplexPost .maximal A r = c ≫ mappingComplexPre .maximal p N :=
    injection_fullMap K x z j
  have hc : eComp SSet.{u} x y z ≫ h = (f ⊗ₘ g) ≫ maxMappingCompose A B D :=
    (K.obj j).map_comp x y z
  have ht₁ : (a ⊗ₘ b) ≫
      (mappingComplexPre .maximal p M ⊗ₘ 𝟙 (mappingComplex .maximal M N)) =
        (a ≫ mappingComplexPre .maximal p M) ⊗ₘ b := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have ht₂ : (f ⊗ₘ b) ≫
      (mappingComplexPost .maximal A q ⊗ₘ 𝟙 (mappingComplex .maximal M N)) =
        (f ≫ mappingComplexPost .maximal A q) ⊗ₘ b := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have ht₃ : (f ⊗ₘ b) ≫
      (𝟙 (mappingComplex .maximal A B) ⊗ₘ mappingComplexPre .maximal q N) =
        f ⊗ₘ (b ≫ mappingComplexPre .maximal q N) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have ht₄ : (f ⊗ₘ g) ≫
      (𝟙 (mappingComplex .maximal A B) ⊗ₘ mappingComplexPost .maximal B r) =
        f ⊗ₘ (g ≫ mappingComplexPost .maximal B r) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  symm
  calc
    ((a ⊗ₘ b) ≫ maxMappingCompose L M N) ≫ mappingComplexPre .maximal p N =
        (a ⊗ₘ b) ≫ ((mappingComplexPre .maximal p M ⊗ₘ 𝟙 (mappingComplex .maximal M N)) ≫
          maxMappingCompose A M N) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => (a ⊗ₘ b) ≫ t) (maxMappingCompose_pre p M N).symm)
    _ = ((a ≫ mappingComplexPre .maximal p M) ⊗ₘ b) ≫ maxMappingCompose A M N :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ maxMappingCompose A M N) ht₁)
    _ = ((f ≫ mappingComplexPost .maximal A q) ⊗ₘ b) ≫ maxMappingCompose A M N :=
      congrArg (fun t => (t ⊗ₘ b) ≫ maxMappingCompose A M N) hp
    _ = (f ⊗ₘ b) ≫ ((mappingComplexPost .maximal A q ⊗ₘ 𝟙 (mappingComplex .maximal M N)) ≫
        maxMappingCompose A M N) :=
      (congrArg (fun t => t ≫ maxMappingCompose A M N) ht₂.symm).trans (Category.assoc _ _ _)
    _ = (f ⊗ₘ b) ≫ ((𝟙 (mappingComplex .maximal A B) ⊗ₘ mappingComplexPre .maximal q N) ≫
        maxMappingCompose A B N) :=
      congrArg (fun t => (f ⊗ₘ b) ≫ t) (maxMappingCompose_middle A q N)
    _ = (f ⊗ₘ (b ≫ mappingComplexPre .maximal q N)) ≫ maxMappingCompose A B N :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ maxMappingCompose A B N) ht₃)
    _ = (f ⊗ₘ (g ≫ mappingComplexPost .maximal B r)) ≫ maxMappingCompose A B N :=
      congrArg (fun t => (f ⊗ₘ t) ≫ maxMappingCompose A B N) hq
    _ = (f ⊗ₘ g) ≫ ((𝟙 (mappingComplex .maximal A B) ⊗ₘ mappingComplexPost .maximal B r) ≫
        maxMappingCompose A B N) :=
      (congrArg (fun t => t ≫ maxMappingCompose A B N) ht₄.symm).trans (Category.assoc _ _ _)
    _ = ((f ⊗ₘ g) ≫ maxMappingCompose A B D) ≫ mappingComplexPost .maximal A r :=
      (congrArg (fun t => (f ⊗ₘ g) ≫ t) (maxMappingCompose_post A B r)).trans
        (Category.assoc _ _ _).symm
    _ = (eComp SSet.{u} x y z ≫ h) ≫ mappingComplexPost .maximal A r :=
      congrArg (fun t => t ≫ mappingComplexPost .maximal A r) hc.symm
    _ = eComp SSet.{u} x y z ≫ (c ≫ mappingComplexPre .maximal p N) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => eComp SSet.{u} x y z ≫ t) hr)
    _ = (eComp SSet.{u} x y z ≫ c) ≫ mappingComplexPre .maximal p N :=
      (Category.assoc _ _ _).symm

end SSet.Marked.EnrichedColimit
