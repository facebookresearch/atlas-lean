/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.EpiInsertion
public import MathlibExt.CategoryTheory.Limits.Shapes.RelativePushoutPasting
public import MathlibExt.CategoryTheory.Reedy.Boundary
public import MathlibExt.CategoryTheory.Reedy.Corner

/-!
# Actual partial degeneracy latching maps and their original relative corners

The full original epi-factor category supplies the diagram of actual simplicial degrees.
Its cocone retains every original degeneracy map. Canonical and caller-chosen complete
cocones give the same natural relative pushout corner. No partial class-preservation or
tensor/model compatibility outcome is an input.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C]

/-- The original partial-factor diagram keeps every original simplicial source object and map. -/
@[implicit_reducible]
def diagram (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) : Index α ⥤ C :=
  inclusion α ⋙ SimplexCategory.reedyOp.latchingDiagram F (Opposite.op ⦋m⦌)

/-- Each partial diagram coefficient is the actual original proper-epi source degree. -/
theorem diagram_obj (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) :
    (diagram F α).obj a = F.obj (source a) := rfl

/-- Every comparison acts by the original unchanged simplicial structure map. -/
theorem diagram_map (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    {a b : Index α} (f : a ⟶ b) : (diagram F α).map f = F.map (comparison f) := rfl

/-- The original partial latching cocone has the actual original degeneracy maps as its legs. -/
def cocone (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) : Cocone (diagram F α) :=
  (SimplexCategory.reedyOp.latchingCocone F (Opposite.op ⦋m⦌)).whisker (inclusion α)

/-- Each partial cocone leg is the original proper degeneracy map into the unchanged full degree. -/
theorem cocone_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) :
    (cocone F α).ι.app a = F.map (arrow a) := rfl

/-- Every original simplicial transformation retains all its partial-factor components. -/
def transformation {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) : diagram F α ⟶ diagram F' α :=
  Functor.whiskerLeft (inclusion α)
    (SimplexCategory.reedyOp.latchingTransformation i (Opposite.op ⦋m⦌))

/-- Each comparison component is the actual original transformation at that degree. -/
theorem transformation_app {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) : (transformation i α).app a = i.app (source a) := rfl

/-- The actual partial latching map out of any caller-chosen complete original cocone. -/
def mapWith (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (c : Cocone (diagram F α)) (hc : IsColimit c) : c.pt ⟶ F.obj (Opposite.op ⦋m⦌) :=
  hc.desc (cocone F α)

/-- Each original caller leg recovers the same original proper degeneracy map. -/
@[reassoc]
theorem mapWith_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (c : Cocone (diagram F α)) (hc : IsColimit c) (a : Index α) :
    c.ι.app a ≫ mapWith F α c hc = F.map (arrow a) := hc.fac _ a

/-- The complete partial colimit comparison between actual caller cocones. -/
def comparisonWith {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) : c.pt ⟶ c'.pt :=
  hc.desc ((Cocone.precompose (transformation i α)).obj c')

/-- Every caller partial comparison leg retains the original coefficient map and target leg. -/
@[reassoc]
theorem comparisonWith_ι {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (a : Index α) :
    c.ι.app a ≫ comparisonWith i α c hc c' = i.app (source a) ≫ c'.ι.app a := hc.fac _ a

/-- All original coefficient maps retain whole partial-latching naturality on caller cocones. -/
theorem mapWith_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c') :
    mapWith F α c hc ≫ i.app (Opposite.op ⦋m⦌) =
      comparisonWith i α c hc c' ≫ mapWith F' α c' hc' := by
  apply hc.hom_ext
  intro a
  calc
    c.ι.app a ≫ (mapWith F α c hc ≫ i.app (Opposite.op ⦋m⦌)) =
        (c.ι.app a ≫ mapWith F α c hc) ≫ i.app (Opposite.op ⦋m⦌) :=
      (Category.assoc _ _ _).symm
    _ = F.map (arrow a) ≫ i.app (Opposite.op ⦋m⦌) :=
      congrArg (fun g ↦ g ≫ i.app (Opposite.op ⦋m⦌)) (mapWith_ι F α c hc a)
    _ = i.app (source a) ≫ F'.map (arrow a) := i.naturality (arrow a)
    _ = i.app (source a) ≫ (c'.ι.app a ≫ mapWith F' α c' hc') :=
      congrArg (fun g ↦ i.app (source a) ≫ g) (mapWith_ι F' α c' hc' a).symm
    _ = (i.app (source a) ≫ c'.ι.app a) ≫ mapWith F' α c' hc' :=
      (Category.assoc _ _ _).symm
    _ = (c.ι.app a ≫ comparisonWith i α c hc c') ≫ mapWith F' α c' hc' :=
      congrArg (fun g ↦ g ≫ mapWith F' α c' hc') (comparisonWith_ι i α c hc c' a).symm
    _ = c.ι.app a ≫ (comparisonWith i α c hc c' ≫ mapWith F' α c' hc') :=
      Category.assoc _ _ _

/-- The actual original relative corner for any complete caller cocones and pushout. -/
def cornerWith {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c'))
    (hp : IsColimit p) : p.pt ⟶ F'.obj (Opposite.op ⦋m⦌) :=
  hp.desc (PushoutCocone.mk (i.app (Opposite.op ⦋m⦌)) (mapWith F' α c' hc')
    (mapWith_naturality i α c hc c' hc'))

/-- The first original caller pushout leg retains the original coefficient transformation. -/
@[reassoc]
theorem cornerWith_inl {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c'))
    (hp : IsColimit p) : p.inl ≫ cornerWith i α c hc c' hc' p hp = i.app (Opposite.op ⦋m⦌) :=
  hp.fac _ WalkingSpan.left

/-- The second original caller pushout leg retains the whole original partial map. -/
@[reassoc]
theorem cornerWith_inr {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c'))
    (hp : IsColimit p) : p.inr ≫ cornerWith i α c hc c' hc' p hp = mapWith F' α c' hc' :=
  hp.fac _ WalkingSpan.right

section Canonical

variable [HasFiniteColimits C]

/-- The original finite partial-factor colimit map into the original full simplicial degree. -/
def map (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    colimit (diagram F α) ⟶ F.obj (Opposite.op ⦋m⦌) :=
  mapWith F α (colimit.cocone _) (colimit.isColimit _)

/-- The canonical partial colimit legs are the unchanged original degeneracy maps. -/
@[reassoc]
theorem map_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) :
    colimit.ι (diagram F α) a ≫ map F α = F.map (arrow a) :=
  mapWith_ι F α (colimit.cocone _) (colimit.isColimit _) a

/-- The complete canonical partial map is natural in every original simplicial transformation. -/
theorem map_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) : map F α ≫ i.app (Opposite.op ⦋m⦌) =
      colimMap (transformation i α) ≫ map F' α :=
  mapWith_naturality i α (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) (colimit.isColimit _)

/-- The actual original partial relative latching corner, on its actual finite pushout. -/
def corner {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    pushout (map F α) (colimMap (transformation i α)) ⟶ F'.obj (Opposite.op ⦋m⦌) :=
  pushout.desc (i.app (Opposite.op ⦋m⦌)) (map F' α) (map_naturality i α)

/-- The first actual partial pushout injection retains the original full coefficient map. -/
@[reassoc]
theorem corner_inl {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    pushout.inl (map F α) (colimMap (transformation i α)) ≫ corner i α =
      i.app (Opposite.op ⦋m⦌) := pushout.inl_desc _ _ _

/-- The second actual partial pushout injection retains the whole original partial map. -/
@[reassoc]
theorem corner_inr {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    pushout.inr (map F α) (colimMap (transformation i α)) ≫ corner i α = map F' α :=
  pushout.inr_desc _ _ _

/-- The partial colimit compares to the original complete latching colimit. -/
def toFull (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    colimit (diagram F α) ⟶ colimit (SimplexCategory.reedyOp.latchingDiagram F (Opposite.op ⦋m⦌)) :=
  colimit.pre _ (inclusion α)

/-- Every comparison into the full latching colimit retains the same original epi label. -/
@[reassoc]
theorem toFull_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) :
    colimit.ι (diagram F α) a ≫ toFull F α =
      colimit.ι (SimplexCategory.reedyOp.latchingDiagram F (Opposite.op ⦋m⦌)) a.obj :=
  colimit.ι_pre _ _ a

/-- The comparison to the full latching object retains the whole original partial map. -/
theorem toFull_map (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    toFull F α ≫ ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌) =
      map F α := by
  apply colimit.hom_ext
  intro a
  calc
    colimit.ι (diagram F α) a ≫
        (toFull F α ≫ ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌)) =
        (colimit.ι (diagram F α) a ≫ toFull F α) ≫
          ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌) :=
      (Category.assoc _ _ _).symm
    _ = colimit.ι (SimplexCategory.reedyOp.latchingDiagram F (Opposite.op ⦋m⦌)) a.obj ≫
        ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌) :=
      congrArg (fun g ↦ g ≫ ReedyStructure.latchingMap SimplexCategory.reedyOp F
        (Opposite.op ⦋m⦌)) (toFull_ι F α a)
    _ = F.map (arrow a) :=
      ReedyStructure.latchingMap_ι SimplexCategory.reedyOp F (Opposite.op ⦋m⦌) a.obj
    _ = colimit.ι (diagram F α) a ≫ map F α := (map_ι F α a).symm

end Canonical

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end

section



/-!
# Actual partial-to-full latching source comparisons

The comparison retains every original epi label and coefficient transformation. Its
relative pushout map factors the actual original partial corner through the full Reedy
corner. Scalar class preservation of the comparison is a separate finite-attachment proof.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- Every original simplicial map preserves the complete partial-to-full colimit comparison. -/
theorem toFull_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    colimMap (transformation i α) ≫ toFull F' α =
      toFull F α ≫ colimMap (SimplexCategory.reedyOp.latchingTransformation i (Opposite.op ⦋m⦌)) :=
          by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, ι_colimMap, Category.assoc, toFull_ι,
    ← Category.assoc, toFull_ι, ι_colimMap]
  rfl

/-- The actual partial source pushout maps to the complete original Reedy source pushout. -/
def toFullCorner {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    pushout (map F α) (colimMap (transformation i α)) ⟶
      pushout (ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌))
        (colimMap (SimplexCategory.reedyOp.latchingTransformation i (Opposite.op ⦋m⦌))) :=
  pushout.map _ _ _ _ (𝟙 (F.obj (Opposite.op ⦋m⦌))) (toFull F' α) (toFull F α)
    ((Category.comp_id _).trans (toFull_map F α).symm) (toFull_naturality i α)

/-- The original coefficient injection remains unchanged under the source enlargement. -/
@[reassoc]
theorem toFullCorner_inl {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    pushout.inl (map F α) (colimMap (transformation i α)) ≫ toFullCorner i α =
      pushout.inl
        (ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌))
        (colimMap (SimplexCategory.reedyOp.latchingTransformation i (Opposite.op ⦋m⦌))) := by
  rw [toFullCorner, pushout.map, pushout.inl_desc, Category.id_comp]

/-- Every original partial target injection retains its complete original full comparison. -/
@[reassoc]
theorem toFullCorner_inr {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    pushout.inr (map F α) (colimMap (transformation i α)) ≫ toFullCorner i α =
      toFull F' α ≫ pushout.inr
        (ReedyStructure.latchingMap SimplexCategory.reedyOp F (Opposite.op ⦋m⦌))
        (colimMap (SimplexCategory.reedyOp.latchingTransformation i (Opposite.op ⦋m⦌))) := by
  rw [toFullCorner, pushout.map, pushout.inr_desc]

/-- The complete original partial corner factors through the complete original Reedy corner. -/
theorem corner_factor_full {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) :
    toFullCorner i α ≫ ReedyStructure.latchingCorner SimplexCategory.reedyOp i
        (Opposite.op ⦋m⦌) = corner i α := by
  apply pushout.hom_ext
  · rw [← Category.assoc, toFullCorner_inl, ReedyStructure.latchingCorner_inl, corner_inl]
  · rw [← Category.assoc, toFullCorner_inr, Category.assoc,
      ReedyStructure.latchingCorner_inr, toFull_map, corner_inr]

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end

section



/-!
# Scalar partial-corner base cases from actual original model laws

The empty partial boundary of an original simplex isomorphism gives exactly the original
component arrow. The full-collapse partial boundary gives exactly the original full Reedy
corner. All complete original pushout and colimit comparisons are retained as Arrow isos.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty Simplicial
open SimplexCategory.PartialLatching

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- The exact empty partial boundary gives the unchanged original coefficient arrow. -/
def cornerComponentArrowIsoOfIsIso {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) [IsIso α] : Arrow.mk (corner i α) ≅ Arrow.mk (i.app (Opposite.op ⦋m⦌)) := by
  let _ : IsIso (colimMap (transformation i α)) :=
    isIso_of_isInitial
      (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (diagram F α)) (colimit.isColimit _))
      (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (diagram F' α)) (colimit.isColimit _)) _
  let p := pushout.inl (map F α) (colimMap (transformation i α))
  letI : IsIso p := by dsimp only [p]; infer_instance
  exact Arrow.isoMk' (corner i α) (i.app (Opposite.op ⦋m⦌)) (asIso p).symm (Iso.refl _) (by
    change inv p ≫ i.app (Opposite.op ⦋m⦌) = corner i α ≫ 𝟙 _
    apply (cancel_epi p).mp
    rw [IsIso.hom_inv_id_assoc, Category.comp_id]
    exact (corner_inl i α).symm)

/-- The original full-collapse partial colimit comparison is an isomorphism on every original leg.
-/
instance toFull_isIso_zero (F : SimplicialObject C) {m : ℕ} (α : ⦋m⦌ ⟶ ⦋0⦌) :
    IsIso (toFull F α) := by
  change IsIso (colimit.pre (SimplexCategory.reedyOp.latchingDiagram F (Opposite.op ⦋m⦌))
    (inclusion α))
  infer_instance

/-- The original full-collapse partial source comparison is the full original pushout isomorphism.
-/
instance toFullCorner_isIso_zero {F F' : SimplicialObject C} (i : F ⟶ F') {m : ℕ}
    (α : ⦋m⦌ ⟶ ⦋0⦌) : IsIso (toFullCorner i α) := by
  dsimp only [toFullCorner]
  infer_instance

/-- The full-collapse partial corner is Arrow-isomorphic to the original full Reedy corner. -/
def cornerFullArrowIsoZero {F F' : SimplicialObject C} (i : F ⟶ F') {m : ℕ}
    (α : ⦋m⦌ ⟶ ⦋0⦌) : Arrow.mk (corner i α) ≅
      Arrow.mk (ReedyStructure.latchingCorner SimplexCategory.reedyOp i (Opposite.op ⦋m⦌)) :=
  Arrow.isoMk' (corner i α) _ (asIso (toFullCorner i α)) (Iso.refl _) (by
    exact (corner_factor_full i α).trans (Category.comp_id (corner i α)).symm)

section Model

variable [ModelCategory C]

/-- All original full cofibration corners derive the actual isomorphism-label partial corner class.
-/
theorem corner_cofibration_of_isIso {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [IsIso α] : cofibrations C (corner i α) :=
  ((cofibrations C).arrow_mk_iso_iff (cornerComponentArrowIsoOfIsIso i α)).mpr
    (ReedyModel.component_cofibration_of_latchingCorners SimplexCategory.reedyOp i hi _)

/-- All original full trivial corners derive the actual isomorphism-label partial trivial class. -/
theorem corner_trivialCofibration_of_isIso {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, trivialCofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [IsIso α] : trivialCofibrations C (corner i α) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (cornerComponentArrowIsoOfIsIso i α)).mpr
    (ReedyModel.component_trivialCofibration_of_latchingCorners SimplexCategory.reedyOp i hi _)

/-- The actual full-collapse partial cofibration is the same original full Reedy cofibration. -/
theorem corner_cofibration_zero {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    {m : ℕ} (α : ⦋m⦌ ⟶ ⦋0⦌) : cofibrations C (corner i α) :=
  ((cofibrations C).arrow_mk_iso_iff (cornerFullArrowIsoZero i α)).mpr (hi _)

/-- The actual full-collapse partial trivial class is the same original full Reedy trivial class. -/
theorem corner_trivialCofibration_zero {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, trivialCofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    {m : ℕ} (α : ⦋m⦌ ⟶ ⦋0⦌) : trivialCofibrations C (corner i α) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (cornerFullArrowIsoZero i α)).mpr (hi _)

end Model

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end

section



/-!
# Exact comparisons for complete caller partial-latching cocones

The source and target caller cocones and the caller pushout retain all their original
legs. Their actual relative corner is Arrow-isomorphic to the canonical relative corner.
Scalar class laws can therefore be transported without changing any original diagram map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- The complete original caller colimit is compared with the canonical original colimit. -/
def callerColimitIso (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (c : Cocone (diagram F α)) (hc : IsColimit c) : c.pt ≅ colimit (diagram F α) :=
  hc.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc]
theorem callerColimitIso_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (c : Cocone (diagram F α)) (hc : IsColimit c) (a : Index α) :
    c.ι.app a ≫ (callerColimitIso F α c hc).hom = colimit.ι (diagram F α) a :=
  hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) a

/-- The original caller partial map is preserved by the whole colimit comparison. -/
theorem callerColimitIso_map (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (c : Cocone (diagram F α)) (hc : IsColimit c) :
    (callerColimitIso F α c hc).hom ≫ map F α = mapWith F α c hc := by
  apply hc.hom_ext
  intro a
  rw [← Category.assoc, callerColimitIso_ι, map_ι, mapWith_ι]

/-- Every original transformation retains its complete caller-to-canonical colimit square. -/
theorem callerColimitIso_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c') :
    comparisonWith i α c hc c' ≫ (callerColimitIso F' α c' hc').hom =
      (callerColimitIso F α c hc).hom ≫ colimMap (transformation i α) := by
  apply hc.hom_ext
  intro a
  rw [← Category.assoc, comparisonWith_ι, Category.assoc, callerColimitIso_ι,
    ← Category.assoc, callerColimitIso_ι, ι_colimMap]
  rfl

/-- The canonical pushout is still the actual pushout of the original caller source maps. -/
theorem callerSpanIsPushout {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c') :
    IsPushout (mapWith F α c hc) (comparisonWith i α c hc c')
      (pushout.inl (map F α) (colimMap (transformation i α)))
      ((callerColimitIso F' α c' hc').hom ≫
        pushout.inr (map F α) (colimMap (transformation i α))) := by
  let e := callerColimitIso F α c hc
  let e' := callerColimitIso F' α c' hc'
  apply (IsPushout.of_hasPushout (map F α) (colimMap (transformation i α))).of_iso
    e.symm (Iso.refl _) e'.symm (Iso.refl _)
  · change map F α ≫ 𝟙 _ = e.inv ≫ mapWith F α c hc
    rw [Category.comp_id, ← callerColimitIso_map F α c hc]
    exact (e.inv_hom_id_assoc _).symm
  · change colimMap (transformation i α) ≫ e'.inv = e.inv ≫ comparisonWith i α c hc c'
    apply (cancel_epi e.hom).mp
    simp only [e.hom_inv_id_assoc]
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, e'.inv_hom_id, Category.comp_id]
    exact (callerColimitIso_naturality i α c hc c' hc').symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [e', Iso.refl_hom, Category.comp_id, Iso.symm_hom] using
      (e'.inv_hom_id_assoc (pushout.inr (map F α) (colimMap (transformation i α)))).symm

/-- The original caller pushout is compared with the exact canonical relative source. -/
def callerSourceIso {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    p.pt ≅ pushout (map F α) (colimMap (transformation i α)) :=
  (IsPushout.of_isColimit hp).isoIsPushout _ _ (callerSpanIsPushout i α c hc c' hc')

@[reassoc]
theorem callerSourceIso_inl {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    p.inl ≫ (callerSourceIso i α c hc c' hc' p hp).hom =
      pushout.inl (map F α) (colimMap (transformation i α)) :=
  (IsPushout.of_isColimit hp).inl_isoIsPushout_hom _ _ _

@[reassoc]
theorem callerSourceIso_inr {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    p.inr ≫ (callerSourceIso i α c hc c' hc' p hp).hom =
      (callerColimitIso F' α c' hc').hom ≫
        pushout.inr (map F α) (colimMap (transformation i α)) :=
  (IsPushout.of_isColimit hp).inr_isoIsPushout_hom _ _ _

/-- The complete original caller corner and canonical corner are the same arrow up to source iso. -/
def callerCornerArrowIso {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    Arrow.mk (cornerWith i α c hc c' hc' p hp) ≅ Arrow.mk (corner i α) :=
  Arrow.isoMk' _ _ (callerSourceIso i α c hc c' hc' p hp) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id]
    apply PushoutCocone.IsColimit.hom_ext hp
    · rw [← Category.assoc, callerSourceIso_inl, corner_inl, cornerWith_inl]
    · rw [← Category.assoc, callerSourceIso_inr, Category.assoc,
        corner_inr, callerColimitIso_map, cornerWith_inr])

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end

section



/-!
# Inverse caller readbacks and scalar class transport

Every inverse colimit and pushout comparison recovers the same original caller leg. The
actual caller-corner class is equivalent to the canonical class by its original Arrow iso.
No partial class-preservation result is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- The inverse comparison retains the original whole caller partial map. -/
theorem callerColimitIso_inv_mapWith (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (c : Cocone (diagram F α)) (hc : IsColimit c) :
    (callerColimitIso F α c hc).inv ≫ mapWith F α c hc = map F α := by
  rw [← callerColimitIso_map F α c hc]
  exact (callerColimitIso F α c hc).inv_hom_id_assoc _

/-- The inverse source comparison retains the original caller coefficient injection. -/
@[reassoc]
theorem callerSourceIso_inv_inl {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    pushout.inl (map F α) (colimMap (transformation i α)) ≫
      (callerSourceIso i α c hc c' hc' p hp).inv = p.inl := by
  apply (cancel_mono (callerSourceIso i α c hc c' hc' p hp).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (callerSourceIso_inl i α c hc c' hc' p hp).symm

/-- The inverse source comparison retains the original caller boundary injection. -/
@[reassoc]
theorem callerSourceIso_inv_inr {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    pushout.inr (map F α) (colimMap (transformation i α)) ≫
      (callerSourceIso i α c hc c' hc' p hp).inv =
        (callerColimitIso F' α c' hc').inv ≫ p.inr := by
  apply (cancel_mono (callerSourceIso i α c hc c' hc' p hp).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [callerSourceIso_inr]
  exact ((callerColimitIso F' α c' hc').inv_hom_id_assoc _).symm

/-- Any scalar class respecting the original Arrow iso has exactly the same caller membership. -/
theorem callerCorner_mem_iff (P : MorphismProperty C) [P.RespectsIso]
    {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    P (cornerWith i α c hc c' hc' p hp) ↔ P (corner i α) :=
  P.arrow_mk_iso_iff (callerCornerArrowIso i α c hc c' hc' p hp)

section Model

variable [ModelCategory C]

/-- The actual model cofibration class is unchanged on the original complete caller corner. -/
theorem callerCorner_cofibration_iff {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    cofibrations C (cornerWith i α c hc c' hc' p hp) ↔ cofibrations C (corner i α) :=
  callerCorner_mem_iff (cofibrations C) i α c hc c' hc' p hp

/-- The actual model trivial class is unchanged on the original complete caller corner. -/
theorem callerCorner_trivialCofibration_iff {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d⦌) (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    trivialCofibrations C (cornerWith i α c hc c' hc' p hp) ↔ trivialCofibrations C (corner i α) :=
  callerCorner_mem_iff (trivialCofibrations C) i α c hc c' hc' p hp

end Model

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end

section



/-!
# Original partial-factor insertion maps on complete caller cocones

Every coefficient map is the original simplicial map. Three complete cocones
of the actual finite factor diagrams suffice; no model structure or global
colimit-preservation assertion enters the construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching SimplexCategory.PartialLatching.Insertion
open SimplexCategory.EpiInsertion

namespace HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

variable {C : Type u} [Category.{v} C]

/-- The complete original source bridge square for each retained residual comparison. -/
theorem sourceBridge_naturality {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ SimplexCategory.adjacentKernel α)
    {a b : Index (res α p hp)} (f : a ⟶ b) :
    comparison f ≫ (SimplexCategory.σ ((arrow b).unop.toOrderHom p)).op =
      (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        comparison ((liftIndex α p hp).map f) := by
  have H := congrArg (fun g ↦ comparison g) ((bridge α p hp).naturality f)
  exact H

/-- The original lifted source diagram gives a complete cocone into any actual old caller cocone. -/
def liftCoconeWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) (c : Cocone (diagram F α)) :
    Cocone (diagram F (res α p hp)) where
  pt := c.pt
  ι.app a := F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
    c.ι.app ((liftIndex α p hp).obj a)
  ι.naturality a b f := by
    change F.map (comparison f) ≫
      (F.map (SimplexCategory.σ ((arrow b).unop.toOrderHom p)).op ≫
        c.ι.app ((liftIndex α p hp).obj b)) =
      (F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        c.ι.app ((liftIndex α p hp).obj a)) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← F.map_comp,
      sourceBridge_naturality α p hp f, F.map_comp, Category.assoc]
    have H := c.w ((liftIndex α p hp).map f)
    exact congrArg (fun z ↦ F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫ z) H

/-- The original lower-to-old intersection map on complete actual caller cocones. -/
def intersectionWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) : cR.pt ⟶ cA.pt :=
  hR.desc (liftCoconeWith F α p hp cA)

/-- Every original intersection leg uses the actual original target codegeneracy. -/
@[reassoc]
theorem intersectionWith_ι (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) (a : Index (res α p hp)) :
    cR.ι.app a ≫ intersectionWith F α p hp cR hR cA =
      F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        cA.ι.app ((liftIndex α p hp).obj a) := hR.fac _ a

/-- The complete original old-factor inclusion on actual caller cocones. -/
def inclusionWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) : cA.pt ⟶ cP.pt :=
  hA.desc (cP.whisker (toPlus α p hp))

/-- Every original old inclusion leg retains the same original epi label. -/
@[reassoc]
theorem inclusionWith_ι (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) (a : Index α) :
    cA.ι.app a ≫ inclusionWith F α p hp cA hA cP = cP.ι.app ((toPlus α p hp).obj a) :=
  hA.fac _ a

/-- The actual original σp injection into the complete new partial-factor cocone. -/
def bottomWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cP : Cocone (diagram F (plus α p hp))) : F.obj (Opposite.op ⦋n⦌) ⟶ cP.pt :=
  cP.ι.app (qObject α p hp)

/-- The actual add-one square keeps every original lower-factor map and caller cocone leg. -/
theorem squareWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) :
    intersectionWith F α p hp cR hR cA ≫ inclusionWith F α p hp cA hA cP =
      mapWith F (res α p hp) cR hR ≫ bottomWith F α p hp cP := by
  apply hR.hom_ext
  intro a
  rw [← Category.assoc, intersectionWith_ι, Category.assoc, inclusionWith_ι,
    ← Category.assoc, mapWith_ι]
  have hl := cP.w (liftBridge α p hp a)
  have hr := cP.w (resToQ α p hp a)
  exact hl.trans hr.symm

/-- The original old partial map is recovered after the complete old-factor inclusion. -/
theorem inclusionWith_mapWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP) :
    inclusionWith F α p hp cA hA cP ≫ mapWith F (plus α p hp) cP hP = mapWith F α cA hA := by
  apply hA.hom_ext
  intro a
  rw [← Category.assoc, inclusionWith_ι, mapWith_ι, mapWith_ι]
  rfl

/-- The actual σp injection recovers the same original whole simplicial degeneracy map. -/
theorem bottomWith_mapWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP) :
    bottomWith F α p hp cP ≫ mapWith F (plus α p hp) cP hP = F.map (SimplexCategory.σ p).op :=
  mapWith_ι F (plus α p hp) cP hP (qObject α p hp)

end HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

end
end
end

section



/-!
# All original coefficient naturality triangles of epi insertion

The four actual insertion-square legs retain every original simplicial
transformation. Complete caller cocones are compared by their original
universal maps, with no preservation or model-structure premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching SimplexCategory.PartialLatching.Insertion
open SimplexCategory.EpiInsertion

namespace HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

variable {C : Type u} [Category.{v} C]

/-- Every original intersection leg retains full naturality in the actual coefficient map. -/
theorem intersectionWith_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cR' : Cocone (diagram F' (res α p hp))) (hR' : IsColimit cR')
    (cA : Cocone (diagram F α)) (hA : IsColimit cA) (cA' : Cocone (diagram F' α)) :
    intersectionWith F α p hp cR hR cA ≫ comparisonWith i α cA hA cA' =
      comparisonWith i (res α p hp) cR hR cR' ≫ intersectionWith F' α p hp cR' hR' cA' := by
  apply hR.hom_ext
  intro a
  calc
    _ = (cR.ι.app a ≫ intersectionWith F α p hp cR hR cA) ≫
        comparisonWith i α cA hA cA' := (Category.assoc _ _ _).symm
    _ = (F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        cA.ι.app ((liftIndex α p hp).obj a)) ≫ comparisonWith i α cA hA cA' := by
      rw [intersectionWith_ι]
    _ = F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        (i.app (source ((liftIndex α p hp).obj a)) ≫
          cA'.ι.app ((liftIndex α p hp).obj a)) := by
      rw [Category.assoc, comparisonWith_ι]
    _ = (F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        i.app (source ((liftIndex α p hp).obj a))) ≫
          cA'.ι.app ((liftIndex α p hp).obj a) := (Category.assoc _ _ _).symm
    _ = (i.app (source a) ≫ F'.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op) ≫
        cA'.ι.app ((liftIndex α p hp).obj a) :=
      congrArg (· ≫ cA'.ι.app ((liftIndex α p hp).obj a))
        (i.naturality (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op)
    _ = i.app (source a) ≫
        (F'.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
          cA'.ι.app ((liftIndex α p hp).obj a)) := Category.assoc _ _ _
    _ = i.app (source a) ≫ (cR'.ι.app a ≫ intersectionWith F' α p hp cR' hR' cA') := by
      rw [intersectionWith_ι]
    _ = (i.app (source a) ≫ cR'.ι.app a) ≫ intersectionWith F' α p hp cR' hR' cA' :=
      (Category.assoc _ _ _).symm
    _ = (cR.ι.app a ≫ comparisonWith i (res α p hp) cR hR cR') ≫
        intersectionWith F' α p hp cR' hR' cA' := by rw [comparisonWith_ι]
    _ = cR.ι.app a ≫ (comparisonWith i (res α p hp) cR hR cR' ≫
        intersectionWith F' α p hp cR' hR' cA') := Category.assoc _ _ _

/-- Every original old-factor inclusion retains full coefficient naturality. -/
theorem inclusionWith_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cA' : Cocone (diagram F' α)) (hA' : IsColimit cA')
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP)
    (cP' : Cocone (diagram F' (plus α p hp))) :
    inclusionWith F α p hp cA hA cP ≫ comparisonWith i (plus α p hp) cP hP cP' =
      comparisonWith i α cA hA cA' ≫ inclusionWith F' α p hp cA' hA' cP' := by
  apply hA.hom_ext
  intro a
  calc
    _ = (cA.ι.app a ≫ inclusionWith F α p hp cA hA cP) ≫
        comparisonWith i (plus α p hp) cP hP cP' := (Category.assoc _ _ _).symm
    _ = cP.ι.app ((toPlus α p hp).obj a) ≫ comparisonWith i (plus α p hp) cP hP cP' := by
      rw [inclusionWith_ι]
    _ = i.app (source a) ≫ cP'.ι.app ((toPlus α p hp).obj a) :=
      comparisonWith_ι i (plus α p hp) cP hP cP' ((toPlus α p hp).obj a)
    _ = i.app (source a) ≫ (cA'.ι.app a ≫ inclusionWith F' α p hp cA' hA' cP') := by
      rw [inclusionWith_ι]
    _ = (i.app (source a) ≫ cA'.ι.app a) ≫ inclusionWith F' α p hp cA' hA' cP' :=
      (Category.assoc _ _ _).symm
    _ = (cA.ι.app a ≫ comparisonWith i α cA hA cA') ≫
        inclusionWith F' α p hp cA' hA' cP' := by rw [comparisonWith_ι]
    _ = cA.ι.app a ≫ (comparisonWith i α cA hA cA' ≫
        inclusionWith F' α p hp cA' hA' cP') := Category.assoc _ _ _

/-- The actual original σp leg retains full coefficient naturality. -/
theorem bottomWith_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP)
    (cP' : Cocone (diagram F' (plus α p hp))) :
    bottomWith F α p hp cP ≫ comparisonWith i (plus α p hp) cP hP cP' =
      i.app (Opposite.op ⦋n⦌) ≫ bottomWith F' α p hp cP' :=
  comparisonWith_ι i (plus α p hp) cP hP cP' (qObject α p hp)

/-- The original lower partial map retains the fourth full coefficient naturality triangle. -/
theorem lowerWith_naturality {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cR' : Cocone (diagram F' (res α p hp))) (hR' : IsColimit cR') :
    mapWith F (res α p hp) cR hR ≫ i.app (Opposite.op ⦋n⦌) =
      comparisonWith i (res α p hp) cR hR cR' ≫ mapWith F' (res α p hp) cR' hR' :=
  mapWith_naturality i (res α p hp) cR hR cR' hR'

end HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

end
end
end

section



/-!
# Complete cocone gluing on the original epi-factor category

Every actual new-index object is either the unchanged old factor or an original
source-codegeneracy factor. Its original comparison triangles give the complete
glued cocone, including all mixed comparisons. No gluing outcome is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching SimplexCategory.PartialLatching.Insertion
open SimplexCategory.EpiInsertion

namespace HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

variable {C : Type u} [Category.{v} C]

/-- Original pushout compatibility retains every actual residual epi's bridge leg. -/
theorem compatibility_ι (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) {X : C} (j : cA.pt ⟶ X)
    (k : F.obj (Opposite.op ⦋n⦌) ⟶ X)
    (hj : intersectionWith F α p hp cR hR cA ≫ j = mapWith F (res α p hp) cR hR ≫ k)
    (a : Index (res α p hp)) :
    F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
      (cA.ι.app ((liftIndex α p hp).obj a) ≫ j) = F.map (arrow a) ≫ k := by
  calc
    _ = (F.map (SimplexCategory.σ ((arrow a).unop.toOrderHom p)).op ≫
        cA.ι.app ((liftIndex α p hp).obj a)) ≫ j := (Category.assoc _ _ _).symm
    _ = (cR.ι.app a ≫ intersectionWith F α p hp cR hR cA) ≫ j := by
      rw [intersectionWith_ι]
    _ = cR.ι.app a ≫ (intersectionWith F α p hp cR hR cA ≫ j) := Category.assoc _ _ _
    _ = cR.ι.app a ≫ (mapWith F (res α p hp) cR hR ≫ k) := congrArg (cR.ι.app a ≫ ·) hj
    _ = (cR.ι.app a ≫ mapWith F (res α p hp) cR hR) ≫ k := (Category.assoc _ _ _).symm
    _ = F.map (arrow a) ≫ k := by rw [mapWith_ι]

/-- The actual glued leg keeps the original old or newly collapsed factor map. -/
def gluedLeg (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) {X : C} (j : cA.pt ⟶ X)
    (k : F.obj (Opposite.op ⦋n⦌) ⟶ X) (a : Index (plus α p hp)) : F.obj (source a) ⟶ X :=
  if ha : p ∈ SimplexCategory.adjacentKernel (arrow a).unop then
    F.map (residual α p hp a ha).op ≫ k
  else cA.ι.app (oldObject α p hp a ha) ≫ j

/-- The original old-factor branch has the unchanged old caller cocone leg. -/
theorem gluedLeg_old (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) {X : C} (j : cA.pt ⟶ X)
    (k : F.obj (Opposite.op ⦋n⦌) ⟶ X) (a : Index (plus α p hp))
    (ha : p ∉ SimplexCategory.adjacentKernel (arrow a).unop) :
    gluedLeg F α p hp cA j k a = cA.ι.app (oldObject α p hp a ha) ≫ j := by
  rw [gluedLeg, dite_eq_right ha]

/-- The original new-factor branch has the original residual epi's degeneracy leg. -/
theorem gluedLeg_new (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cA : Cocone (diagram F α)) {X : C} (j : cA.pt ⟶ X)
    (k : F.obj (Opposite.op ⦋n⦌) ⟶ X) (a : Index (plus α p hp))
    (ha : p ∈ SimplexCategory.adjacentKernel (arrow a).unop) :
    gluedLeg F α p hp cA j k a = F.map (residual α p hp a ha).op ≫ k := by
  rw [gluedLeg, dite_eq_left ha]

/-- All mixed original comparison maps recover the original target codegeneracy triangle. -/
theorem mixed_comparison_op {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ SimplexCategory.adjacentKernel α)
    {a b : Index (plus α p hp)} (ha : p ∈ SimplexCategory.adjacentKernel (arrow a).unop)
    (hb : p ∉ SimplexCategory.adjacentKernel (arrow b).unop) (f : a ⟶ b) :
    comparison f = (SimplexCategory.σ ((residual α p hp a ha).toOrderHom p)).op ≫
      comparison (mixedLiftToOld α p hp ha hb f) := by
  apply Quiver.Hom.unop_inj
  rw [unop_comp]
  exact (mixedComparison_target p (arrow b).unop hb (residual α p hp a ha)
    (comparison f).unop (mixed_equation α p hp ha f)).symm

/-- The complete glued legs retain naturality on every original new-factor comparison. -/
theorem gluedLeg_naturality (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) {X : C} (j : cA.pt ⟶ X)
    (k : F.obj (Opposite.op ⦋n⦌) ⟶ X)
    (hj : intersectionWith F α p hp cR hR cA ≫ j = mapWith F (res α p hp) cR hR ≫ k)
    {a b : Index (plus α p hp)} (f : a ⟶ b) :
    F.map (comparison f) ≫ gluedLeg F α p hp cA j k b = gluedLeg F α p hp cA j k a := by
  by_cases ha : p ∈ SimplexCategory.adjacentKernel (arrow a).unop
  · by_cases hb : p ∈ SimplexCategory.adjacentKernel (arrow b).unop
    · rw [gluedLeg_new F α p hp cA j k b hb, gluedLeg_new F α p hp cA j k a ha,
        ← Category.assoc, ← F.map_comp]
      have H : comparison f ≫ (residual α p hp b hb).op = (residual α p hp a ha).op := by
        apply Quiver.Hom.unop_inj
        rw [unop_comp]
        exact residual_comparison α p hp ha hb f
      rw [H]
    · rw [gluedLeg_old F α p hp cA j k b hb, gluedLeg_new F α p hp cA j k a ha]
      let aR := mixedResidualObject α p hp ha hb f
      have hc := cA.w (mixedLiftToOld α p hp ha hb f)
      have hcompat := compatibility_ι F α p hp cR hR cA j k hj aR
      calc
        _ = (F.map (SimplexCategory.σ ((residual α p hp a ha).toOrderHom p)).op ≫
            F.map (comparison (mixedLiftToOld α p hp ha hb f))) ≫
            (cA.ι.app (oldObject α p hp b hb) ≫ j) := by
          rw [mixed_comparison_op α p hp ha hb f, F.map_comp]
        _ = F.map (SimplexCategory.σ ((residual α p hp a ha).toOrderHom p)).op ≫
            ((F.map (comparison (mixedLiftToOld α p hp ha hb f)) ≫
              cA.ι.app (oldObject α p hp b hb)) ≫ j) := by
          simp only [Category.assoc]
        _ = F.map (SimplexCategory.σ ((residual α p hp a ha).toOrderHom p)).op ≫
            (cA.ι.app ((liftIndex α p hp).obj aR) ≫ j) := congrArg
          (fun z ↦ F.map (SimplexCategory.σ ((residual α p hp a ha).toOrderHom p)).op ≫ (z ≫ j)) hc
        _ = F.map (residual α p hp a ha).op ≫ k := hcompat
  · by_cases hb : p ∈ SimplexCategory.adjacentKernel (arrow b).unop
    · exact (ha (comparison_kernel_subset f hb)).elim
    · rw [gluedLeg_old F α p hp cA j k b hb, gluedLeg_old F α p hp cA j k a ha,
        ← Category.assoc]
      exact congrArg (· ≫ j) (cA.w (oldHom α p hp ha hb f))

/-- The actual compatible old and σp legs form a complete cocone on the original full new index. -/
def gluedCocone (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) {X : C} (j : cA.pt ⟶ X)
    (k : F.obj (Opposite.op ⦋n⦌) ⟶ X)
    (hj : intersectionWith F α p hp cR hR cA ≫ j = mapWith F (res α p hp) cR hR ≫ k) :
    Cocone (diagram F (plus α p hp)) where
  pt := X
  ι.app a := gluedLeg F α p hp cA j k a
  ι.naturality a b f := by
    change F.map (comparison f) ≫ gluedLeg F α p hp cA j k b =
      gluedLeg F α p hp cA j k a ≫ 𝟙 _
    rw [Category.comp_id]
    exact gluedLeg_naturality F α p hp cR hR cA j k hj f

end HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

end
end
end

section



/-!
# Actual add-one epi-factor pushouts on complete caller cocones

The complete original new factor colimit has the pushout universal property
of the original lower intersection, old-factor inclusion and σp injection.
The mediator is constructed on every original epi label and comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.PartialLatching SimplexCategory.PartialLatching.Insertion
open SimplexCategory.EpiInsertion

namespace HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

variable {C : Type u} [Category.{v} C]

/-- The actual mediator is the universal map from the complete original new factor cocone. -/
def pushoutDescWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α))
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP)
    (s : PushoutCocone (intersectionWith F α p hp cR hR cA)
      (mapWith F (res α p hp) cR hR)) : cP.pt ⟶ s.pt :=
  hP.desc (gluedCocone F α p hp cR hR cA s.inl s.inr s.condition)

/-- The constructed mediator retains the whole actual old caller cocone leg. -/
theorem pushoutDescWith_left (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP)
    (s : PushoutCocone (intersectionWith F α p hp cR hR cA)
      (mapWith F (res α p hp) cR hR)) :
    inclusionWith F α p hp cA hA cP ≫ pushoutDescWith F α p hp cR hR cA cP hP s = s.inl := by
  apply hA.hom_ext
  intro a
  rw [← Category.assoc, inclusionWith_ι]
  change cP.ι.app ((toPlus α p hp).obj a) ≫
    hP.desc (gluedCocone F α p hp cR hR cA s.inl s.inr s.condition) = cA.ι.app a ≫ s.inl
  rw [hP.fac]
  change gluedLeg F α p hp cA s.inl s.inr ((toPlus α p hp).obj a) = _
  rw [gluedLeg_old F α p hp cA s.inl s.inr ((toPlus α p hp).obj a)
    (old_not_collapsed α p hp a)]
  rfl

/-- The constructed mediator retains the same original whole σp injection leg. -/
theorem pushoutDescWith_right (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α))
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP)
    (s : PushoutCocone (intersectionWith F α p hp cR hR cA)
      (mapWith F (res α p hp) cR hR)) :
    bottomWith F α p hp cP ≫ pushoutDescWith F α p hp cR hR cA cP hP s = s.inr := by
  change cP.ι.app (qObject α p hp) ≫
    hP.desc (gluedCocone F α p hp cR hR cA s.inl s.inr s.condition) = s.inr
  rw [hP.fac]
  change gluedLeg F α p hp cA s.inl s.inr (qObject α p hp) = s.inr
  rw [gluedLeg_new F α p hp cA s.inl s.inr (qObject α p hp) (qObject_collapsed α p hp),
    residual_qObject]
  have hi : F.map (𝟙 ⦋n⦌).op = 𝟙 (F.obj (Opposite.op ⦋n⦌)) :=
    F.map_id (Opposite.op ⦋n⦌)
  exact (congrArg (· ≫ s.inr) hi).trans (Category.id_comp _)

/-- Every mediator on the actual new factor colimit is determined by its two original pushout legs.
-/
theorem pushoutDescWith_unique (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP)
    (s : PushoutCocone (intersectionWith F α p hp cR hR cA)
      (mapWith F (res α p hp) cR hR)) (m : cP.pt ⟶ s.pt)
    (hl : inclusionWith F α p hp cA hA cP ≫ m = s.inl)
    (hr : bottomWith F α p hp cP ≫ m = s.inr) :
    m = pushoutDescWith F α p hp cR hR cA cP hP s := by
  apply hP.hom_ext
  intro a
  change cP.ι.app a ≫ m = cP.ι.app a ≫
    hP.desc (gluedCocone F α p hp cR hR cA s.inl s.inr s.condition)
  rw [hP.fac]
  change cP.ι.app a ≫ m = gluedLeg F α p hp cA s.inl s.inr a
  by_cases ha : p ∈ SimplexCategory.adjacentKernel (arrow a).unop
  · rw [gluedLeg_new F α p hp cA s.inl s.inr a ha]
    have hw := cP.w (residualToQ α p hp a ha)
    calc
      _ = (F.map (residual α p hp a ha).op ≫ cP.ι.app (qObject α p hp)) ≫ m :=
        congrArg (· ≫ m) hw.symm
      _ = F.map (residual α p hp a ha).op ≫ (bottomWith F α p hp cP ≫ m) := Category.assoc _ _ _
      _ = F.map (residual α p hp a ha).op ≫ s.inr := congrArg (F.map (residual α p hp a ha).op ≫ ·)
          hr
  · rw [gluedLeg_old F α p hp cA s.inl s.inr a ha]
    let b := oldObject α p hp a ha
    have hb : cA.ι.app b ≫ inclusionWith F α p hp cA hA cP = cP.ι.app a := by
      rw [inclusionWith_ι]
      rfl
    calc
      _ = (cA.ι.app b ≫ inclusionWith F α p hp cA hA cP) ≫ m := congrArg (· ≫ m) hb.symm
      _ = cA.ι.app b ≫ (inclusionWith F α p hp cA hA cP ≫ m) := Category.assoc _ _ _
      _ = cA.ι.app b ≫ s.inl := congrArg (cA.ι.app b ≫ ·) hl

/-- The complete actual new-factor caller cocone has the original add-one pushout universal
property. -/
def pushoutIsColimitWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP) :
    IsColimit (PushoutCocone.mk (inclusionWith F α p hp cA hA cP) (bottomWith F α p hp cP)
      (squareWith F α p hp cR hR cA hA cP)) :=
  PushoutCocone.IsColimit.mk _
    (pushoutDescWith F α p hp cR hR cA cP hP)
    (pushoutDescWith_left F α p hp cR hR cA hA cP hP)
    (pushoutDescWith_right F α p hp cR hR cA cP hP)
    (pushoutDescWith_unique F α p hp cR hR cA hA cP hP)

/-- The whole original add-one factor-category square is an actual pushout for all complete caller
cocones. -/
theorem isPushoutWith (F : SimplicialObject C) {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α)
    (cR : Cocone (diagram F (res α p hp))) (hR : IsColimit cR)
    (cA : Cocone (diagram F α)) (hA : IsColimit cA)
    (cP : Cocone (diagram F (plus α p hp))) (hP : IsColimit cP) :
    IsPushout (intersectionWith F α p hp cR hR cA) (mapWith F (res α p hp) cR hR)
      (inclusionWith F α p hp cA hA cP) (bottomWith F α p hp cP) :=
  IsPushout.of_isColimit (pushoutIsColimitWith F α p hp cR hR cA hA cP hP)

end HomotopicalAlgebra.PartialDegeneracyLatching.Insertion

end
end
end

section



/-!
# Actual relative insertion data for the original partial degeneracy corners

The source squares are the proved original epi-factor-category pushouts. Every entry of
the relative attachment is an original simplicial map or its original finite colimit map.
No partial scalar class or pushout outcome is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.EpiInsertion

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- The two genuine add-one pushouts retain every original coefficient transformation. -/
@[implicit_reducible]
def insertionData {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) : RelativePushoutPasting.Data C where
  I := colimit (diagram F (res α p hp))
  J := colimit (diagram F α)
  V := F.obj (Opposite.op ⦋n⦌)
  K := colimit (diagram F (plus α p hp))
  I' := colimit (diagram F' (res α p hp))
  J' := colimit (diagram F' α)
  V' := F'.obj (Opposite.op ⦋n⦌)
  K' := colimit (diagram F' (plus α p hp))
  X := F.obj (Opposite.op ⦋n + 1⦌)
  v := Insertion.intersectionWith F α p hp (colimit.cocone _) (colimit.isColimit _)
      (colimit.cocone _)
  u := map F (res α p hp)
  j := Insertion.inclusionWith F α p hp (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _)
  k := Insertion.bottomWith F α p hp (colimit.cocone _)
  square := Insertion.isPushoutWith F α p hp (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _)
  v' := Insertion.intersectionWith F' α p hp (colimit.cocone _) (colimit.isColimit _)
      (colimit.cocone _)
  u' := map F' (res α p hp)
  j' := Insertion.inclusionWith F' α p hp (colimit.cocone _) (colimit.isColimit _)
      (colimit.cocone _)
  k' := Insertion.bottomWith F' α p hp (colimit.cocone _)
  square' := Insertion.isPushoutWith F' α p hp (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _)
  iI := colimMap (transformation i (res α p hp))
  iJ := colimMap (transformation i α)
  iV := i.app (Opposite.op ⦋n⦌)
  iK := colimMap (transformation i (plus α p hp))
  v_iJ := Insertion.intersectionWith_naturality i α p hp
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _)
  u_iV := map_naturality i (res α p hp)
  j_iK := Insertion.inclusionWith_naturality i α p hp
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _)
  k_iK := Insertion.bottomWith_naturality i α p hp
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _)
  a := map F α
  b := F.map (SimplexCategory.σ p).op
  g := map F (plus α p hp)
  j_g := Insertion.inclusionWith_mapWith F α p hp
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _)
  k_g := Insertion.bottomWith_mapWith F α p hp (colimit.cocone _) (colimit.isColimit _)

/-- The original lower relative corner is exactly the source piece being attached. -/
theorem insertionData_lowerCorner {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) :
    (insertionData i α p hp).lowerCorner = corner i (res α p hp) := rfl

/-- The original enlarged relative corner is the same unchanged plus-label corner. -/
theorem insertionData_enlargedCorner {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) :
    (insertionData i α p hp).enlargedCorner (i.app (Opposite.op ⦋n + 1⦌))
      (map F' (plus α p hp)) (map_naturality i (plus α p hp)) = corner i (plus α p hp) := rfl

/-- The original old corner is recovered by the complete actual target inclusion comparison. -/
theorem insertionData_oldCorner {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) :
    (insertionData i α p hp).oldCorner (i.app (Opposite.op ⦋n + 1⦌))
      (map F' (plus α p hp)) (map_naturality i (plus α p hp)) = corner i α := by
  apply pushout.hom_ext
  · rw [RelativePushoutPasting.Data.oldCorner_inl]
    exact (corner_inl i α).symm
  · rw [RelativePushoutPasting.Data.oldCorner_inr]
    dsimp only [insertionData]
    rw [corner_inr]
    exact Insertion.inclusionWith_mapWith F' α p hp
      (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _)

/-- The actual relative source enlargement keeps the original source degree and both labels. -/
def insertionToNext {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) :
    pushout (map F α) (colimMap (transformation i α)) ⟶
      pushout (map F (plus α p hp)) (colimMap (transformation i (plus α p hp))) :=
  (insertionData i α p hp).toLarge

/-- The actual old partial corner factors through the actual enlarged partial corner. -/
theorem insertionToNext_corner {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) :
    insertionToNext i α p hp ≫ corner i (plus α p hp) = corner i α := by
  rw [← insertionData_oldCorner i α p hp, ← insertionData_enlargedCorner i α p hp]
  exact (insertionData i α p hp).toLarge_enlargedCorner _ _ _

/-- Ordinary scalar cobase-change closure gives the class of this actual source enlargement. -/
theorem insertionToNext_mem (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    {F F' : SimplicialObject C} (i : F ⟶ F') {n d : ℕ}
    (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α] (p : Fin (n + 1))
    (hp : p ∉ SimplexCategory.adjacentKernel α) (h : P (corner i (res α p hp))) :
    P (insertionToNext i α p hp) :=
  (insertionData i α p hp).toLarge_mem P h

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end

section



/-!
# Actual scalar classes of every original partial degeneracy corner

Induction on source degree and then target degree derives the class from the original full
Reedy corners. A genuine missing adjacent pair gives the proved add-one pushout; its actual
relative source enlargement is a cobase change of the actual lower-degree corner. Ordinary
composition finishes the step. No partial preservation or arbitrary colimit closure is a
premise, and the model category requires only its original finite colimits.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Simplicial
open SimplexCategory.EpiInsertion

namespace HomotopicalAlgebra.PartialDegeneracyLatching

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- The original full corners and ordinary scalar cobase-change/composition laws suffice. -/
theorem corner_mem_of_latchingCorners (P : MorphismProperty C)
    [P.IsStableUnderCobaseChange] [P.IsStableUnderComposition]
    {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ j, P (ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [Epi α] : P (corner i α) := by
  have H : ∀ m d (α : ⦋m⦌ ⟶ ⦋d⦌), Epi α → P (corner i α) := by
    intro m
    induction m with
    | zero =>
      intro d α hepi
      let _ : Epi α := hepi
      have hd : d = 0 := Nat.eq_zero_of_le_zero (SimplexCategory.le_of_epi α)
      subst d
      exact (P.arrow_mk_iso_iff (cornerFullArrowIsoZero i α)).mpr (hi _)
    | succ n ihn =>
      intro d
      induction d with
      | zero =>
        intro α _
        exact (P.arrow_mk_iso_iff (cornerFullArrowIsoZero i α)).mpr (hi _)
      | succ d ihd =>
        intro α hepi
        let _ : Epi α := hepi
        obtain ⟨p, hp⟩ := SimplexCategory.exists_not_mem_adjacentKernel_of_epi_positive α
        have hres : P (corner i (res α p hp)) := ihn d (res α p hp) inferInstance
        have hplus : P (corner i (plus α p hp)) := ihd (plus α p hp) inferInstance
        rw [← insertionToNext_corner i α p hp]
        exact P.comp_mem _ _ (insertionToNext_mem P i α p hp hres) hplus
  exact H m d α inferInstance

section Model

variable [ModelCategory C]

/-- Every original epi-label partial corner of a genuine Reedy cofibration is a cofibration. -/
theorem corner_cofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ j, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [Epi α] : cofibrations C (corner i α) :=
  corner_mem_of_latchingCorners (cofibrations C) i hi α

/-- Every original epi-label partial corner of a genuine trivial Reedy map is trivial. -/
theorem corner_trivialCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ j, trivialCofibrations C
      (ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [Epi α] : trivialCofibrations C (corner i α) :=
  corner_mem_of_latchingCorners (trivialCofibrations C) i hi α

/-- Complete caller cocones retain the same original partial cofibration class. -/
theorem cornerWith_cofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ j, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [Epi α]
    (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    cofibrations C (cornerWith i α c hc c' hc' p hp) :=
  (callerCorner_cofibration_iff i α c hc c' hc' p hp).mpr (corner_cofibration i hi α)

/-- Complete caller cocones retain the same original partial trivial cofibration class. -/
theorem cornerWith_trivialCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ j, trivialCofibrations C
      (ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [Epi α]
    (c : Cocone (diagram F α)) (hc : IsColimit c)
    (c' : Cocone (diagram F' α)) (hc' : IsColimit c')
    (p : PushoutCocone (mapWith F α c hc) (comparisonWith i α c hc c')) (hp : IsColimit p) :
    trivialCofibrations C (cornerWith i α c hc c' hc' p hp) :=
  (callerCorner_trivialCofibration_iff i α c hc c' hc' p hp).mpr (corner_trivialCofibration i hi α)

end Model

end HomotopicalAlgebra.PartialDegeneracyLatching

end
end
end
