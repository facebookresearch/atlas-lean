/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ExternalModule
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ModuleGeneratorLaws

/-!
# The full ordinary Day module and external-action presentation

Every module recovers its original external coefficient action. Conversely,
complete external data descend to the actual module. Morphisms keep their
entire original natural transformations and all coefficient squares.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uI vI uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory.MonoidalCategory.DayFunctor.ExternalModule

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [∀ F G : I ⥤ V, (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (X : V) (i : I), PreservesColimitsOfShape (CostructuredArrow (tensor I) i) (tensorLeft X)]
  [∀ (X : V) (i : I), PreservesColimitsOfShape (CostructuredArrow (tensor I) i) (tensorRight X)]
  [∀ (X : V) (i : I),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) i) (tensorLeft X)]
  [∀ (X : V) (i : I),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) i) (tensorRight X)]
  [∀ (X : V) (i : I × I),
    PreservesColimitsOfShape (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) i)
      (tensorRight X)]
  [∀ (X : V) (i : I × I),
    PreservesColimitsOfShape (CostructuredArrow ((tensor I).prod (𝟭 I)) i) (tensorRight X)]
  (S : DayFunctor I V) [MonObj S]

/-- The original complete coefficient action of a Day module. -/
abbrev pair (M : Mod (DayFunctor I V) S) (a n : I) :
    S.functor.obj a ⊗ M.X.functor.obj n ⟶ M.X.functor.obj (a ⊗ n) :=
  (DayFunctor.η S M.X).app (a, n) ≫ M.mod.smul.natTrans.app (a ⊗ n)

/-- Complete coefficient squares construct an actual module morphism. -/
def moduleHomOfCoefficients (M N : Mod (DayFunctor I V) S)
    (f : M.X.functor ⟶ N.X.functor)
    (h : ∀ a n : I, pair S M a n ≫ f.app (a ⊗ n) =
      (S.functor.obj a ◁ f.app n) ≫ pair S N a n) : M ⟶ N where
  hom := DayFunctor.Hom.mk f
  isModHom :=
    { smul_hom := by
        apply DayFunctor.tensor_hom_ext
        intro a n
        have hη := DayFunctor.tensorHom_η (𝟙 S) (DayFunctor.Hom.mk f) a n
        simp only [DayFunctor.id_natTrans, NatTrans.id_app, id_tensorHom] at hη
        exact (Category.assoc _ _ _).symm.trans
          ((h a n).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ N.mod.smul.natTrans.app (a ⊗ n)) hη).symm.trans
              (Category.assoc _ _ _)))) }

/-- Every actual module map preserves all of its original coefficient actions. -/
theorem pair_morphism {M N : Mod (DayFunctor I V) S} (f : M ⟶ N) (a n : I) :
    pair S M a n ≫ f.hom.natTrans.app (a ⊗ n) =
      (S.functor.obj a ◁ f.hom.natTrans.app n) ≫ pair S N a n := by
  have hc := congrArg (fun t => (DayFunctor.η S M.X).app (a, n) ≫ t.natTrans.app (a ⊗ n))
    (IsModHom.smul_hom (A := S) (f := f.hom))
  have hη := DayFunctor.tensorHom_η (𝟙 S) f.hom a n
  simp only [DayFunctor.id_natTrans, NatTrans.id_app, id_tensorHom] at hη
  exact (Category.assoc _ _ _).trans
    (hc.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ N.mod.smul.natTrans.app (a ⊗ n)) hη).trans
        (Category.assoc _ _ _))))

/-- Every actual Day module supplies its full original external diagram and action laws. -/
def ofModule (M : Mod (DayFunctor I V) S) : Data S where
  diagram := M.X.functor
  action := DayFunctor.η S M.X ≫ Functor.whiskerLeft (tensor I) M.mod.smul.natTrans
  unit n := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using!
      LawfulDayConvolutionMonoidalCategoryStruct.modulePairUnit
        (C₀ := I) (V₀ := V) (D₀ := DayFunctor I V) S M.X n
  assoc a b n := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using!
      LawfulDayConvolutionMonoidalCategoryStruct.modulePairMul
        (C₀ := I) (V₀ := V) (D₀ := DayFunctor I V) S M.X a b n

namespace Data

variable {S}

/-- A morphism of external data is the whole original diagram map with every coefficient square. -/
@[ext]
structure Hom (d e : Data S) where
  /-- The unchanged original finite-index natural transformation. -/
  map : d.diagram ⟶ e.diagram
  /-- Every full external coefficient action commutes with the same original map. -/
  comm (a n : I) : d.action.app (a, n) ≫ map.app (a ⊗ n) =
    (S.functor.obj a ◁ map.app n) ≫ e.action.app (a, n)

/-- Complete external data form a category with their original natural transformations. -/
instance : Category (Data S) where
  Hom := Hom
  id d := { map := 𝟙 d.diagram, comm := by intro a n; simp }
  comp f g :=
    { map := f.map ≫ g.map
      comm := by
        intro a n
        simp only [NatTrans.comp_app, whiskerLeft_comp, Category.assoc]
        rw [← Category.assoc, f.comm, Category.assoc, g.comm] }
  id_comp := by intro d e f; apply Hom.ext; exact Category.id_comp f.map
  comp_id := by intro d e f; apply Hom.ext; exact Category.comp_id f.map
  assoc := by intro c d e f r s t; apply Hom.ext; exact Category.assoc r.map s.map t.map

/-- Every original external-data map gives a genuine module map through the same Day descent. -/
def toModuleMap {d e : Data S} (f : d ⟶ e) : d.toModule ⟶ e.toModule :=
  moduleHomOfCoefficients S d.toModule e.toModule f.map (by
    intro a n
    exact (congrArg (fun t => t ≫ f.map.app (a ⊗ n)) (d.toModule_generator a n)).trans
      ((f.comm a n).trans
        (congrArg (fun t => (S.functor.obj a ◁ f.map.app n) ≫ t) (e.toModule_generator a n).symm)))

/-- Every module map supplies the full original external-data map. -/
def ofModuleMap {M N : Mod (DayFunctor I V) S} (f : M ⟶ N) : ofModule S M ⟶ ofModule S N :=
  { map := f.hom.natTrans, comm := pair_morphism S f }

end Data

/-- The complete external-action construction is functorial on original objects and maps. -/
def toModules : Data S ⥤ Mod (DayFunctor I V) S where
  obj := Data.toModule
  map := Data.toModuleMap
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

/-- The complete coefficient extraction is functorial on all original modules and module maps. -/
def fromModules : Mod (DayFunctor I V) S ⥤ Data S where
  obj := ofModule S
  map := Data.ofModuleMap
  map_id _ := by apply Data.Hom.ext; rfl
  map_comp _ _ := by apply Data.Hom.ext; rfl

/-- The original external action is recovered on every whole coefficient generator. -/
def unitIsoApp (d : Data S) : d ≅ (fromModules S).obj ((toModules S).obj d) where
  hom :=
    { map := 𝟙 d.diagram
      comm := by
        intro a n
        have h : (ofModule S d.toModule).action.app (a, n) = d.action.app (a, n) :=
          d.toModule_generator a n
        have hi : (S.functor.obj a ◁ 𝟙 (d.diagram.obj n)) ≫
            (ofModule S d.toModule).action.app (a, n) = (ofModule S d.toModule).action.app (a, n) :=
          (congrArg (fun t => t ≫ (ofModule S d.toModule).action.app (a, n))
            (whiskerLeft_id (S.functor.obj a) (d.diagram.obj n))).trans (Category.id_comp _)
        exact (Category.comp_id _).trans (h.symm.trans hi.symm) }
  inv :=
    { map := 𝟙 d.diagram
      comm := by
        intro a n
        have h : (ofModule S d.toModule).action.app (a, n) = d.action.app (a, n) :=
          d.toModule_generator a n
        have hi : (S.functor.obj a ◁ 𝟙 (d.diagram.obj n)) ≫ d.action.app (a, n) =
            d.action.app (a, n) :=
          (congrArg (fun t => t ≫ d.action.app (a, n))
            (whiskerLeft_id (S.functor.obj a) (d.diagram.obj n))).trans (Category.id_comp _)
        exact (Category.comp_id _).trans (h.trans hi.symm) }
  hom_inv_id := by apply Data.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply Data.Hom.ext; exact Category.id_comp _

/-- The original complete Day action is recovered by its actual generator universal property. -/
def counitIsoApp (M : Mod (DayFunctor I V) S) :
    (toModules S).obj ((fromModules S).obj M) ≅ M where
  hom := moduleHomOfCoefficients S (ofModule S M).toModule M (𝟙 M.X.functor) (by
    intro a n
    have h : pair S (ofModule S M).toModule a n = pair S M a n :=
      (ofModule S M).toModule_generator a n
    have hi : (S.functor.obj a ◁ 𝟙 (M.X.functor.obj n)) ≫ pair S M a n = pair S M a n :=
      (congrArg (fun t => t ≫ pair S M a n)
        (whiskerLeft_id (S.functor.obj a) (M.X.functor.obj n))).trans (Category.id_comp _)
    exact (Category.comp_id _).trans (h.trans hi.symm))
  inv := moduleHomOfCoefficients S M (ofModule S M).toModule (𝟙 M.X.functor) (by
    intro a n
    have h : pair S (ofModule S M).toModule a n = pair S M a n :=
      (ofModule S M).toModule_generator a n
    have hi : (S.functor.obj a ◁ 𝟙 (M.X.functor.obj n)) ≫ pair S (ofModule S M).toModule a n =
        pair S (ofModule S M).toModule a n :=
      (congrArg (fun t => t ≫ pair S (ofModule S M).toModule a n)
        (whiskerLeft_id (S.functor.obj a) (M.X.functor.obj n))).trans (Category.id_comp _)
    exact (Category.comp_id _).trans (h.symm.trans hi.symm))
  hom_inv_id := by apply Mod.hom_ext; exact Category.id_comp _
  inv_hom_id := by apply Mod.hom_ext; exact Category.id_comp _

/-- The full external-action reconstruction is natural in every original diagram map. -/
def unitIso : 𝟭 (Data S) ≅ toModules S ⋙ fromModules S :=
  NatIso.ofComponents (unitIsoApp S) (by
    intro d e f
    apply Data.Hom.ext
    exact (Category.comp_id f.map).trans (Category.id_comp f.map).symm)

/-- The full Day-module reconstruction is natural in every original module map. -/
def counitIso : fromModules S ⋙ toModules S ≅ 𝟭 (Mod (DayFunctor I V) S) :=
  NatIso.ofComponents (counitIsoApp S) (by
    intro M N f
    apply Mod.hom_ext
    exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

/-- Actual complete external data and actual ordinary Day modules are equivalent. -/
def equivalence : Data S ≌ Mod (DayFunctor I V) S where
  functor := toModules S
  inverse := fromModules S
  unitIso := unitIso S
  counitIso := counitIso S
  functor_unitIso_comp d := by apply Mod.hom_ext; exact Category.id_comp _

/-- The complete external-to-module comparison retains the original whole diagram. -/
theorem equivalence_functor_carrier (d : Data S) :
    ((equivalence S).functor.obj d).X.functor = d.diagram := rfl

/-- The complete module-to-external comparison retains the original whole diagram. -/
theorem equivalence_inverse_diagram (M : Mod (DayFunctor I V) S) :
    ((equivalence S).inverse.obj M).diagram = M.X.functor := rfl

/-- The entire forward Hom function retains every original diagram-map component. -/
theorem equivalence_functor_map {d e : Data S} (f : d ⟶ e) :
    ((equivalence S).functor.map f).hom.natTrans = f.map := rfl

/-- The entire inverse Hom function retains every original module-map component. -/
theorem equivalence_inverse_map {M N : Mod (DayFunctor I V) S} (f : M ⟶ N) :
    ((equivalence S).inverse.map f).map = f.hom.natTrans := rfl

end CategoryTheory.MonoidalCategory.DayFunctor.ExternalModule
