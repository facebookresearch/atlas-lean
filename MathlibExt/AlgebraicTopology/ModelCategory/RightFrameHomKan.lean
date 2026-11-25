/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy

/-!
# Actual finite partial face-matching categories

For a supplied set of original codimension-one face indices, retain the full
original opposite-simplex matching subcategory on the proper monomorphisms
whose original image omits one selected vertex. All original Under triangles
and all original simplex maps are retained. Horn matching is the specialization
to every original face index except the supplied horn index.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w

open CategoryTheory Limits MorphismProperty Simplicial Opposite

namespace SimplexCategory.PartialMatching

/-- The original proper mono omits one of the original selected face indices. -/
def Faces (n : ℕ) (J : Finset (Fin (n + 1))) :
    ObjectProperty (reedyOp.Matching (op ⦋n⦌)) := fun a =>
  ∃ j : Fin (n + 1), j ∈ J ∧ j ∉ Set.range (reedyOp.matchingArrow a).unop.toOrderHom

/-- The full original matching subcategory of the selected original faces. -/
abbrev Index (n : ℕ) (J : Finset (Fin (n + 1))) := (Faces n J).FullSubcategory

/-- The original full inclusion, retaining every original object and comparison triangle. -/
abbrev inclusion (n : ℕ) (J : Finset (Fin (n + 1))) : Index n J ⥤ reedyOp.Matching (op ⦋n⦌) :=
  (Faces n J).ι

/-- The original opposite-simplex target of every retained proper mono. -/
abbrev target {n : ℕ} {J : Finset (Fin (n + 1))} (a : Index n J) : SimplexCategoryᵒᵖ :=
  reedyOp.matchingTarget a.obj

/-- The unchanged original incoming simplex face, in its original opposite category. -/
def arrow {n : ℕ} {J : Finset (Fin (n + 1))} (a : Index n J) : op ⦋n⦌ ⟶ target a :=
  reedyOp.matchingArrow a.obj

/-- Every original retained matching comparison has its original opposite-simplex arrow. -/
def comparison {n : ℕ} {J : Finset (Fin (n + 1))} {a b : Index n J} (f : a ⟶ b) :
    target a ⟶ target b := reedyOp.matchingComparison f.hom

/-- Every original retained matching arrow is an actual original simplex monomorphism. -/
instance arrow_mono {n : ℕ} {J : Finset (Fin (n + 1))} (a : Index n J) : Mono (arrow a).unop :=
  (reedyOp_inverse _).1 a.obj.obj.hom.property

/-- Each original retained proper mono has strictly smaller actual original degree. -/
theorem target_lt {n : ℕ} {J : Finset (Fin (n + 1))} (a : Index n J) : (target a).unop.len < n :=
  a.obj.property

/-- All original matching comparison triangles retain their unchanged original equality. -/
@[reassoc]
theorem arrow_comparison {n : ℕ} {J : Finset (Fin (n + 1))} {a b : Index n J} (f : a ⟶ b) :
    arrow a ≫ comparison f = arrow b := reedyOp.matchingArrow_comparison f.hom

/-- Actual partial face matching objects are finite because the original matching category is
finite. -/
instance finiteIndex (n : ℕ) (J : Finset (Fin (n + 1))) : Finite (Index n J) :=
  Finite.of_injective (fun a : Index n J => a.obj)
      (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

/-- Actual partial face matching morphism types are finite, with every original triangle retained.
-/
instance finiteIndexHom (n : ℕ) (J : Finset (Fin (n + 1))) (a b : Index n J) : Finite (a ⟶ b) :=
  Finite.of_injective (fun f : a ⟶ b => f.hom) (fun _ _ h => ObjectProperty.hom_ext (Faces n J) h)

/-- The exact partial face matching category is an actual finite category. -/
instance indexFinCategory (n : ℕ) (J : Finset (Fin (n + 1))) : FinCategory (Index n J) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- Every positive horn retains all original codimension-one face indices except its supplied
missing one. -/
abbrev HornIndex (n : ℕ) (k : Fin (n + 1)) := Index n (Finset.univ.erase k)

/-- An actual retained horn face has its unchanged original simplex in the original horn. -/
theorem horn_label_mem (n : ℕ) (k : Fin (n + 1)) (a : HornIndex n k) :
    SSet.stdSimplex.objEquiv.{w}.symm (arrow a).unop ∈
      (SSet.horn.{w} n k).obj (target a) := by
  rcases a.property with ⟨j, hj, hmiss⟩
  rw [SSet.mem_horn_iff_notMem_range]
  refine ⟨j, (Finset.mem_erase.mp hj).1, ?_⟩
  exact hmiss

/-- Each selected original codimension-one face is retained as the same actual matching object. -/
def faceMk {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∈ J) :
    Index (n + 1) J := by
  let a := reedyOp.matchingMk (SimplexCategory.δ j).op
    ((reedyOp_inverse _).2 inferInstance) (Nat.lt_succ_self n)
  refine ⟨a, j, hj, ?_⟩
  change j ∉ Set.range (SimplexCategory.δ j).toOrderHom
  change j ∉ Set.range j.succAbove
  rw [Fin.range_succAbove]
  simp

/-- Every original selected face retains its original opposite-simplex endpoint. -/
theorem target_faceMk {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∈ J) :
    target (faceMk J j hj) = op ⦋n⦌ := rfl

/-- Every original selected face retains its same original opposite coface map. -/
theorem arrow_faceMk {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∈ J) :
    arrow (faceMk J j hj) = (SimplexCategory.δ j).op := rfl

/-- Enlarging the selected original face family retains each actual object and every original
triangle. -/
def ofSubset (n : ℕ) {J K : Finset (Fin (n + 1))} (h : J ⊆ K) : Index n J ⥤ Index n K where
  obj a := ⟨a.obj, by rcases a.property with ⟨j, hj, hp⟩; exact ⟨j, h hj, hp⟩⟩
  map f := ObjectProperty.homMk f.hom

/-- An empty original face family has an empty actual matching index. -/
instance emptyIndex_isEmpty (n : ℕ) : IsEmpty (Index n ∅) :=
  ⟨fun a => by rcases a.property with ⟨j, hj, _⟩; exact (Finset.notMem_empty j hj).elim⟩

end SimplexCategory.PartialMatching

end
end
end

section



/-! # Actual original finite partial face-matching cones and maps -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.PartialFaceMatching

variable {C : Type u} [Category.{v} C]

/-- The actual original coefficient diagram on all retained original face maps. -/
@[implicit_reducible]
def diagram (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1))) :
    SimplexCategory.PartialMatching.Index n J ⥤ C :=
  SimplexCategory.PartialMatching.inclusion n J ⋙ SimplexCategory.reedyOp.matchingDiagram B (op ⦋n⦌)

/-- The original partial matching cone retains all original simplex face maps. -/
def cone (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1))) : Cone (diagram B n J) :=
  (SimplexCategory.reedyOp.matchingCone B (op ⦋n⦌)).whisker
      (SimplexCategory.PartialMatching.inclusion n J)

/-- Every original partial cone leg remains the original coefficient face map. -/
theorem cone_π (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1)))
    (a : SimplexCategory.PartialMatching.Index n J) :
    (cone B n J).π.app a = B.map (SimplexCategory.PartialMatching.arrow a) := rfl

/-- The original simplicial transformation restricted to all original partial face maps. -/
def transformation {B B' : SimplicialObject C} (f : B ⟶ B') (n : ℕ) (J : Finset (Fin (n + 1))) :
    diagram B n J ⟶ diagram B' n J :=
  Functor.whiskerLeft (SimplexCategory.PartialMatching.inclusion n J)
    (SimplexCategory.reedyOp.matchingTransformation f (op ⦋n⦌))

/-- Each original coefficient transformation retains the whole original partial face component. -/
theorem transformation_app {B B' : SimplicialObject C} (f : B ⟶ B') (n : ℕ)
    (J : Finset (Fin (n + 1))) (a : SimplexCategory.PartialMatching.Index n J) :
    (transformation f n J).app a = f.app (SimplexCategory.PartialMatching.target a) := rfl

/-- The partial matching map from every caller complete original cone. -/
def mapWith (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1)))
    (c : Cone (diagram B n J)) (hc : IsLimit c) : B.obj (op ⦋n⦌) ⟶ c.pt := hc.lift (cone B n J)

/-- Each original caller projection recovers the original face coefficient map. -/
@[reassoc]
theorem mapWith_π (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1)))
    (c : Cone (diagram B n J)) (hc : IsLimit c) (a : SimplexCategory.PartialMatching.Index n J) :
    mapWith B n J c hc ≫ c.π.app a = B.map (SimplexCategory.PartialMatching.arrow a) := hc.fac _ a

section Canonical

variable [HasFiniteLimits C]

/-- The actual finite original partial matching object. -/
abbrev object (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1))) := limit (diagram B n J)

/-- The actual original partial matching map using only its actual finite limit. -/
def map (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1))) : B.obj (op ⦋n⦌) ⟶ object B n J
    :=
  mapWith B n J (limit.cone _) (limit.isLimit _)

/-- Every canonical projection retains the original coefficient and original simplex map. -/
@[reassoc]
theorem map_π (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1)))
    (a : SimplexCategory.PartialMatching.Index n J) :
    map B n J ≫ limit.π (diagram B n J) a = B.map (SimplexCategory.PartialMatching.arrow a) :=
  mapWith_π B n J (limit.cone _) (limit.isLimit _) a

/-- The whole original partial matching map is natural in every original coefficient transformation.
-/
@[reassoc]
theorem map_naturality {B B' : SimplicialObject C} (f : B ⟶ B') (n : ℕ) (J : Finset (Fin (n + 1))) :
    map B n J ≫ limMap (transformation f n J) = f.app (op ⦋n⦌) ≫ map B' n J := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, limMap_π, ← Category.assoc, map_π, Category.assoc, map_π]
  exact f.naturality (SimplexCategory.PartialMatching.arrow a)

/-- The original partial face restriction between the actual finite matching limits. -/
def projection (B : SimplicialObject C) (n : ℕ) {J K : Finset (Fin (n + 1))} (h : J ⊆ K) :
    object B n K ⟶ object B n J :=
  limit.pre (diagram B n K) (SimplexCategory.PartialMatching.ofSubset n h)

/-- Every original face projection is retained by the actual partial restriction. -/
@[reassoc]
theorem projection_π (B : SimplicialObject C) (n : ℕ) {J K : Finset (Fin (n + 1))} (h : J ⊆ K)
    (a : SimplexCategory.PartialMatching.Index n J) :
    projection B n h ≫ limit.π (diagram B n J) a =
      limit.π (diagram B n K) ((SimplexCategory.PartialMatching.ofSubset n h).obj a) :=
  limit.pre_π _ _ a

/-- All original coefficient face maps retain their whole partial restriction equation. -/
@[reassoc]
theorem map_projection (B : SimplicialObject C) (n : ℕ) {J K : Finset (Fin (n + 1))} (h : J ⊆ K) :
    map B n K ≫ projection B n h = map B n J := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, projection_π, map_π]
  exact map_π B n K ((SimplexCategory.PartialMatching.ofSubset n h).obj a)

/-- The actual original codimension-one face projection from a partial matching object. -/
def faceProjection (B : SimplicialObject C) {n : ℕ} (J : Finset (Fin (n + 2)))
    (j : Fin (n + 2)) (hj : j ∈ J) : object B (n + 1) J ⟶ B.obj (op ⦋n⦌) :=
  limit.π (diagram B (n + 1) J) (SimplexCategory.PartialMatching.faceMk J j hj)

/-- The original face projection reads back the same original simplicial face map. -/
@[reassoc]
theorem map_faceProjection (B : SimplicialObject C) {n : ℕ} (J : Finset (Fin (n + 2)))
    (j : Fin (n + 2)) (hj : j ∈ J) : map B (n + 1) J ≫ faceProjection B J j hj = B.δ j :=
  map_π B (n + 1) J (SimplexCategory.PartialMatching.faceMk J j hj)

/-- The actual horn matching object, retaining all original horn face indices. -/
abbrev hornObject (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1)) := object B n
    (Finset.univ.erase k)

/-- The actual original horn matching map. -/
def hornMap (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1)) :
    B.obj (op ⦋n⦌) ⟶ hornObject B n k := map B n (Finset.univ.erase k)

/-- Every original horn face projection retains its same original face coefficient map. -/
@[reassoc]
theorem hornMap_π (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (a : SimplexCategory.PartialMatching.HornIndex n k) :
    hornMap B n k ≫ limit.π (diagram B n (Finset.univ.erase k)) a =
      B.map (SimplexCategory.PartialMatching.arrow a) := map_π B n _ a

end Canonical

end HomotopicalAlgebra.PartialFaceMatching

end
end
end

section



/-!
# Original Reedy-fibrant simplicial diagrams are fibrant in every degree

The terminal target has an actual terminal matching limit. The complete
original matching corner of the terminal projection is Arrow-isomorphic
to the original matching map. The genuine source Reedy boundary law then
derives every original coefficient fibration. No arbitrary limit-class
closure or objectwise fibrancy outcome is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.RightFrameHornGeometry

variable {C : Type u} [Category.{v} C]

section Geometry

variable [HasFiniteLimits C]

/-- The original terminal coefficient diagram. -/
abbrev terminalDiagram : SimplicialObject C := (Functor.const SimplexCategoryᵒᵖ).obj (terminal C)

/-- Every original simplicial object has its unchanged original terminal projection. -/
def terminalProjection (B : SimplicialObject C) : B ⟶ terminalDiagram (C := C) where
  app j := terminal.from (B.obj j)
  naturality _ _ _ := terminalIsTerminal.hom_ext _ _

/-- The original complete terminal-coefficient matching cone has its exact original diagram type. -/
def terminalMatchingCone (j : SimplexCategoryᵒᵖ) (X : C) :
    Cone (SimplexCategory.reedyOp.matchingDiagram (terminalDiagram (C := C)) j) where
  pt := X
  π.app _ := terminal.from X
  π.naturality _ _ _ := terminalIsTerminal.hom_ext _ _

/-- The actual original matching limit of the terminal diagram is terminal. -/
def terminalMatchingIsTerminal (j : SimplexCategoryᵒᵖ) :
    IsTerminal (limit (SimplexCategory.reedyOp.matchingDiagram (terminalDiagram (C := C)) j)) :=
  IsTerminal.ofUniqueHom
    (fun X => limit.lift _ (terminalMatchingCone j X))
    (fun X m => by
      apply limit.hom_ext
      intro a
      exact terminalIsTerminal.hom_ext _ _)

/-- The actual matching map of the terminal coefficient is the original terminal isomorphism. -/
theorem terminalMatchingMap_isIso (j : SimplexCategoryᵒᵖ) :
    IsIso (ReedyStructure.matchingMap SimplexCategory.reedyOp (terminalDiagram (C := C)) j) :=
  isIso_of_isTerminal terminalIsTerminal (terminalMatchingIsTerminal j) _

/-- The original complete matching corner of the terminal projection is the original matching map.
-/
def terminalProjectionMatchingCornerIso (B : SimplicialObject C) (j : SimplexCategoryᵒᵖ) :
    Arrow.mk (ReedyStructure.matchingCorner SimplexCategory.reedyOp (terminalProjection B) j) ≅
      Arrow.mk (ReedyStructure.matchingMap SimplexCategory.reedyOp B j) := by
  letI := terminalMatchingMap_isIso (C := C) j
  let e := asIso (pullback.fst
    (limMap (SimplexCategory.reedyOp.matchingTransformation (terminalProjection B) j))
    (ReedyStructure.matchingMap SimplexCategory.reedyOp (terminalDiagram (C := C)) j))
  refine Arrow.isoMk (Iso.refl _) e ?_
  change 𝟙 (B.obj j) ≫ ReedyStructure.matchingMap SimplexCategory.reedyOp B j =
    ReedyStructure.matchingCorner SimplexCategory.reedyOp (terminalProjection B) j ≫
      pullback.fst _ _
  rw [Category.id_comp]
  exact (ReedyStructure.matchingCorner_fst SimplexCategory.reedyOp (terminalProjection B) j).symm

end Geometry

section Model

variable [ModelCategory C]

/-- The original full matching fibrations derive a genuine fibration at every original coefficient.
-/
theorem degree_isFibrant (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (j : SimplexCategoryᵒᵖ) : IsFibrant (B.obj j) := by
  have hc : ∀ k, fibrations C
      (ReedyStructure.matchingCorner SimplexCategory.reedyOp (terminalProjection B) k) :=
    fun k => ((fibrations C).arrow_mk_iso_iff (terminalProjectionMatchingCornerIso B k)).2 (hB k)
  have h := ReedyModel.component_fibration_of_matchingCorners SimplexCategory.reedyOp
    (terminalProjection B) hc j
  exact (fibration_iff _).2 h

/-- The actual empty partial matching object is terminal, with its original cone. -/
def emptyPartialMatchingIsTerminal (B : SimplicialObject C) (n : ℕ) :
    IsTerminal (PartialFaceMatching.object B n ∅) :=
  isLimitEquivIsTerminalOfIsEmpty C (limit.cone (PartialFaceMatching.diagram B n ∅))
      (limit.isLimit _)

/-- The actual empty partial matching map is a genuine source fibration from the original full Reedy
data. -/
theorem emptyPartialMatching_fibration (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (n : ℕ) : fibrations C (PartialFaceMatching.map B n ∅) := by
  have h := (isFibrant_iff_of_isTerminal (PartialFaceMatching.map B n ∅)
    (emptyPartialMatchingIsTerminal B n)).1 (degree_isFibrant B hB (op ⦋n⦌))
  exact (fibration_iff _).1 h

end Model

end HomotopicalAlgebra.RightFrameHornGeometry

end
end
end

section



/-! # The whole selected face family is the original complete matching category -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace SimplexCategory.PartialMatching

/-- Every actual original proper mono omits an original vertex, so belongs to the full face family.
-/
theorem fullFaceProperty (n : ℕ) (a : reedyOp.Matching (op ⦋n⦌)) : Faces n Finset.univ a := by
  classical
  have h : ¬Function.Surjective (reedyOp.matchingArrow a).unop.toOrderHom := by
    intro hs
    have hc := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at hc
    exact Nat.not_le_of_lt a.property (Nat.le_of_succ_le_succ hc)
  obtain ⟨j, hj⟩ := not_forall.mp h
  exact ⟨j, Finset.mem_univ j, hj⟩

/-- The original full face inclusion is a genuine equivalence, retaining all original maps. -/
instance fullInclusion_isEquivalence (n : ℕ) : (inclusion n Finset.univ).IsEquivalence where
  essSurj := { mem_essImage a := ⟨⟨a, fullFaceProperty n a⟩, ⟨Iso.refl _⟩⟩ }

end SimplexCategory.PartialMatching

namespace HomotopicalAlgebra.PartialFaceMatching

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- The original full matching limit maps by its unchanged inclusion to the full selected-face
limit. -/
def fromFull (B : SimplicialObject C) (n : ℕ) :
    limit (SimplexCategory.reedyOp.matchingDiagram B (op ⦋n⦌)) ⟶ object B n Finset.univ :=
  limit.pre _ (SimplexCategory.PartialMatching.inclusion n Finset.univ)

/-- The original complete matching boundary and full selected-face boundary are isomorphic by the
same inclusion. -/
theorem fromFull_isIso (B : SimplicialObject C) (n : ℕ) : IsIso (fromFull B n) := by
  dsimp only [fromFull]
  infer_instance

/-- Every original selected-face projection retains the original whole matching projection. -/
@[reassoc]
theorem fromFull_π (B : SimplicialObject C) (n : ℕ)
    (a : SimplexCategory.PartialMatching.Index n Finset.univ) :
    fromFull B n ≫ limit.π (diagram B n Finset.univ) a =
      limit.π (SimplexCategory.reedyOp.matchingDiagram B (op ⦋n⦌)) a.obj := limit.pre_π _ _ a

/-- The whole actual original matching map retains its same full-face restriction. -/
@[reassoc]
theorem matchingMap_fromFull (B : SimplicialObject C) (n : ℕ) :
    ReedyStructure.matchingMap SimplexCategory.reedyOp B (op ⦋n⦌) ≫ fromFull B n = map B n
        Finset.univ := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, fromFull_π, ReedyStructure.matchingMap_π, map_π]
  rfl

end HomotopicalAlgebra.PartialFaceMatching

namespace HomotopicalAlgebra.RightFrameHornGeometry

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The full selected-face map is a genuine source fibration from the original Reedy matching data.
-/
theorem fullPartialMatching_fibration (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j)) (n : ℕ) :
    fibrations C (PartialFaceMatching.map B n Finset.univ) := by
  let _ := PartialFaceMatching.fromFull_isIso B n
  rw [← PartialFaceMatching.matchingMap_fromFull]
  exact (fibrations C).comp_mem _ _ (hB _) ((fibrations C).of_isIso _)

end HomotopicalAlgebra.RightFrameHornGeometry

end
end
end

section



/-!
# Actual original resolution Hom horn cones

Every actual horn map into the original right resolution Hom gives a cone
on the original finite horn matching category. All original proper mono
labels, matching comparison triangles, simplicial actions, and limit
projections are retained. An actual matching lift reads back every original
horn face in the original SSet.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.RightFrameHornGeometry

/-- Every original horn matching object retains its original simplex label in the actual horn. -/
def hornLabel (n : ℕ) (k : Fin (n + 1)) (a : SimplexCategory.PartialMatching.HornIndex n k) :
    (SSet.horn.{v} n k : SSet.{v}).obj (SimplexCategory.PartialMatching.target a) :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialMatching.arrow a).unop,
    SimplexCategory.PartialMatching.horn_label_mem n k a⟩

/-- Every original matching comparison retains the same original horn simplex operator. -/
theorem hornLabel_comparison (n : ℕ) (k : Fin (n + 1))
    {a b : SimplexCategory.PartialMatching.HornIndex n k} (f : a ⟶ b) :
    (SSet.horn.{v} n k : SSet.{v}).map (SimplexCategory.PartialMatching.comparison f)
        (hornLabel n k a) =
      hornLabel n k b := by
  apply Subtype.ext
  change SSet.stdSimplex.objEquiv.symm
      ((SimplexCategory.PartialMatching.comparison f).unop ≫
          (SimplexCategory.PartialMatching.arrow a).unop) = _
  apply congrArg SSet.stdSimplex.objEquiv.symm
  exact congrArg Quiver.Hom.unop (SimplexCategory.PartialMatching.arrow_comparison f)

variable {C : Type u} [Category.{v} C]

/-- Every original horn coordinate has its exact original coefficient-Hom endpoint. -/
def hornCoordinate (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (a : SimplexCategory.PartialMatching.HornIndex n k) :
    X ⟶ B.obj (SimplexCategory.PartialMatching.target a) :=
  z.app (SimplexCategory.PartialMatching.target a) (hornLabel n k a)

/-- All original horn coordinates retain their original matching naturality. -/
theorem hornCoordinate_naturality (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    {a b : SimplexCategory.PartialMatching.HornIndex n k} (f : a ⟶ b) :
    hornCoordinate X B n k z b = hornCoordinate X B n k z a ≫ B.map
        (SimplexCategory.PartialMatching.comparison f) := by
  have hl := congrArg (fun x => z.app (SimplexCategory.PartialMatching.target b) x)
    (hornLabel_comparison n k f)
  have hn := z.naturality_apply (SimplexCategory.PartialMatching.comparison f) (hornLabel n k a)
  exact (hl.symm.trans hn).trans
    (ResolutionHomComplex.right_map_apply X B (SimplexCategory.PartialMatching.comparison f)
      (hornCoordinate X B n k z a))

/-- The actual original Hom horn map defines all original coefficient face coordinates of a finite
matching cone. -/
def hornHomCone (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    Cone (PartialFaceMatching.diagram B n (Finset.univ.erase k)) where
  pt := X
  π.app a := hornCoordinate X B n k z a
  π.naturality {_a _b} f := (Category.id_comp _).trans (hornCoordinate_naturality X B n k z f)

/-- Every original horn-cone projection is the actual original Hom-map coordinate. -/
theorem hornHomCone_π (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (a : SimplexCategory.PartialMatching.HornIndex n k) :
    (hornHomCone X B n k z).π.app a = z.app (SimplexCategory.PartialMatching.target a)
        (hornLabel n k a) := rfl

variable [HasFiniteLimits C]

/-- The whole actual original finite matching map associated to an original Hom horn. -/
def hornHomMap (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    X ⟶ PartialFaceMatching.hornObject B n k :=
  limit.lift _ (hornHomCone X B n k z)

/-- Every original matching projection recovers the original Hom horn coordinate. -/
@[reassoc]
theorem hornHomMap_π (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (a : SimplexCategory.PartialMatching.HornIndex n k) :
    hornHomMap X B n k z ≫ limit.π (PartialFaceMatching.diagram B n (Finset.univ.erase k)) a =
      z.app (SimplexCategory.PartialMatching.target a) (hornLabel n k a) := limit.lift_π _ a

/-- Each actual coefficient map gives its original complete standard-simplex map in the original
right Hom. -/
def homSimplex (X : C) (B : SimplicialObject C) (n : ℕ) (f : X ⟶ B.obj (op ⦋n⦌)) :
    (Δ[n] : SSet.{v}) ⟶ ResolutionHomComplex.right X B := SSet.yonedaEquiv.symm f

omit [HasFiniteLimits C] in
/-- Every original standard-simplex coordinate is the original postcomposition by the same simplex
map. -/
theorem homSimplex_app (X : C) (B : SimplicialObject C) (n : ℕ) (f : X ⟶ B.obj (op ⦋n⦌))
    (k : Fin (n + 1)) (a : SimplexCategory.PartialMatching.HornIndex n k) :
    (homSimplex X B n f).app (SimplexCategory.PartialMatching.target a)
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialMatching.arrow a).unop) =
      f ≫ B.map (SimplexCategory.PartialMatching.arrow a) := by
  exact (SSet.yonedaEquiv_symm_app_objEquiv_symm (X := ResolutionHomComplex.right X B) f
    (SimplexCategory.PartialMatching.arrow a).unop).trans
    (ResolutionHomComplex.right_map_apply X B (SimplexCategory.PartialMatching.arrow a) f)

/-- Every selected original codimension-one horn face is the original native horn simplex. -/
theorem hornLabel_faceMk {n : ℕ} (k j : Fin (n + 2)) (hj : j ≠ k) :
    hornLabel.{v} (n + 1) k (SimplexCategory.PartialMatching.faceMk (Finset.univ.erase k) j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)) = SSet.horn.face k j hj := by
  apply Subtype.ext
  rfl

/-- Every original matching lift recovers the original horn coordinate at every original mono face.
-/
theorem hornMatchingLift_π (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 1))
    (z : (SSet.horn.{v} n k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (f : X ⟶ B.obj (op ⦋n⦌)) (hf : f ≫ PartialFaceMatching.hornMap B n k = hornHomMap X B n k z)
    (a : SimplexCategory.PartialMatching.HornIndex n k) :
    f ≫ B.map (SimplexCategory.PartialMatching.arrow a) = hornCoordinate X B n k z a := by
  have h := congrArg
      (fun u => u ≫ limit.π (PartialFaceMatching.diagram B n (Finset.univ.erase k)) a) hf
  simpa only [Category.assoc, PartialFaceMatching.hornMap_π, hornHomMap_π, hornCoordinate] using h

/-- An actual finite horn-matching lift extends the original horn map in every positive dimension
and every
horn index. -/
theorem homSimplex_horn_extension (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (f : X ⟶ B.obj (op ⦋n + 1⦌))
    (hf : f ≫ PartialFaceMatching.hornMap B (n + 1) k = hornHomMap X B (n + 1) k z) :
    (SSet.horn.{v} (n + 1) k).ι ≫ homSimplex X B (n + 1) f = z := by
  apply SSet.horn.hom_ext
  intro j hj
  let a := SimplexCategory.PartialMatching.faceMk (Finset.univ.erase k) j
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  have ha := hornLabel_faceMk k j hj
  have h := hornMatchingLift_π X B (n + 1) k z f hf a
  change (homSimplex X B (n + 1) f).app (op ⦋n⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ j)) =
    z.app (op ⦋n⦌) (SSet.horn.face k j hj)
  rw [← ha]
  exact (homSimplex_app X B (n + 1) f k a).trans h

end HomotopicalAlgebra.RightFrameHornGeometry

end
end
end

section



/-! # Original coface residuals and finite selected face families -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Simplicial

namespace SimplexCategory.FaceSubdivision

/-- The original simplex residual through the supplied original coface. -/
def cofaceFactor {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) : x ⟶ ⦋n⦌ := SimplexCategory.factor_δ f j

/-- The actual original residual retains its complete original composition equation. -/
theorem cofaceFactor_spec {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) :
    cofaceFactor f j ≫ SimplexCategory.δ j = f :=
  SimplexCategory.factor_δ_spec f j hj

/-- Every original vertex is recovered by the actual increasing original coface. -/
theorem cofaceFactor_apply {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) (t : Fin (x.len + 1)) :
    j.succAbove ((cofaceFactor f j).toOrderHom t) = f.toOrderHom t := by
  have h := SimplexCategory.congr_toOrderHom_apply (cofaceFactor_spec f j hj) t
  change j.succAbove ((cofaceFactor f j).toOrderHom t) = f.toOrderHom t at h
  exact h

/-- Residuals of original monomorphisms remain genuine original monomorphisms. -/
theorem cofaceFactor_mono {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌) [Mono f]
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) : Mono (cofaceFactor f j) := by
  have : Mono (cofaceFactor f j ≫ SimplexCategory.δ j) := by
    rw [cofaceFactor_spec f j hj]
    infer_instance
  exact mono_of_mono (cofaceFactor f j) (SimplexCategory.δ j)

/-- The original coface monomorphism determines the whole original residual uniquely. -/
theorem cofaceFactor_unique {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) (g : x ⟶ ⦋n⦌)
    (h : g ≫ SimplexCategory.δ j = f) : g = cofaceFactor f j := by
  apply (cancel_mono (SimplexCategory.δ j)).mp
  exact h.trans (cofaceFactor_spec f j hj).symm

/-- All original comparison arrows retain their exact original residual triangle. -/
theorem comp_cofaceFactor {x y : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) (g : y ⟶ x) :
    g ≫ cofaceFactor f j = cofaceFactor (g ≫ f) j := by
  have hjg : ∀ t, (g ≫ f).toOrderHom t ≠ j := fun t => hj (g.toOrderHom t)
  apply (cancel_mono (SimplexCategory.δ j)).mp
  rw [Category.assoc, cofaceFactor_spec f j hj, cofaceFactor_spec (g ≫ f) j hjg]

/-- Original omitted vertices correspond exactly to omitted residual vertices. -/
theorem cofaceFactor_omits_iff {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) (r : Fin (n + 1)) :
    j.succAbove r ∉ Set.range f.toOrderHom ↔
      r ∉ Set.range (cofaceFactor f j).toOrderHom := by
  constructor
  · intro hmiss hmem
    obtain ⟨t, ht⟩ := hmem
    apply hmiss
    exact ⟨t, (cofaceFactor_apply f j hj t).symm.trans (congrArg j.succAbove ht)⟩
  · intro hmiss hmem
    obtain ⟨t, ht⟩ := hmem
    apply hmiss
    exact ⟨t, Fin.succAbove_right_injective ((cofaceFactor_apply f j hj t).trans ht)⟩

/-- The supplied original coface has its literal identity residual. -/
theorem cofaceFactor_coface {n : ℕ} (j : Fin (n + 2)) :
    cofaceFactor (SimplexCategory.δ j) j = 𝟙 ⦋n⦌ := by
  have hj : ∀ t, (SimplexCategory.δ j).toOrderHom t ≠ j := by
    intro t
    change j.succAbove t ≠ j
    exact Fin.succAbove_ne _ _
  symm
  apply cofaceFactor_unique (SimplexCategory.δ j) j hj
  exact Category.id_comp _

/-- The exact lower face family under the original supplied increasing coface. -/
def lowerFaces {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    Finset (Fin (n + 1)) := Finset.univ.filter fun r => j.succAbove r ∈ J

@[simp]
theorem mem_lowerFaces {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (r : Fin (n + 1)) : r ∈ lowerFaces J j ↔ j.succAbove r ∈ J := by
  simp [lowerFaces]

/-- The original increasing coface recovers exactly the old original selected family. -/
theorem image_lowerFaces {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    (lowerFaces J j).image j.succAbove = J := by
  ext s
  constructor
  · intro hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    exact (mem_lowerFaces J j r).mp hr
  · intro hs
    have hsj : s ≠ j := fun h => hj (h ▸ hs)
    have hrange : s ∈ Set.range j.succAbove := by
      rw [Fin.range_succAbove]
      exact hsj
    obtain ⟨r, hr⟩ := hrange
    exact Finset.mem_image.mpr ⟨r, (mem_lowerFaces J j r).mpr (hr ▸ hs), hr⟩

@[simp]
theorem lowerFaces_empty {n : ℕ} (j : Fin (n + 2)) : lowerFaces ∅ j = ∅ := by
  simp [lowerFaces]

@[simp]
theorem lowerFaces_univ {n : ℕ} (j : Fin (n + 2)) : lowerFaces Finset.univ j = Finset.univ := by
  simp [lowerFaces]

/-- Every original residual inclusion retains the supplied selected-face inclusion. -/
theorem lowerFaces_mono {n : ℕ} {J K : Finset (Fin (n + 2))} (h : J ⊆ K) (j : Fin (n + 2)) :
    lowerFaces J j ⊆ lowerFaces K j := by
  intro r hr
  exact (mem_lowerFaces K j r).mpr (h ((mem_lowerFaces J j r).mp hr))

/-- A genuine original mono omitting a vertex has strictly smaller original degree. -/
theorem lt_of_mono_omits {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n⦌) [Mono f]
    (r : Fin (n + 1)) (hr : ∀ t, f.toOrderHom t ≠ r) : x.len < n := by
  have hinj : Function.Injective f.toOrderHom := SimplexCategory.mono_iff_injective.mp inferInstance
  have himage : Finset.univ.image f.toOrderHom ⊆ (Finset.univ : Finset (Fin (n + 1))).erase r := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_erase.mpr ⟨hr t, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card himage
  have hle : x.len + 1 ≤ n := by
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ r), Nat.add_sub_cancel] using hcard
  exact (Nat.lt_succ_self x.len).trans_le hle

/-- The original coface residual retains strict degree on the actual overlap. -/
theorem cofaceFactor_lt {x : SimplexCategory} {n : ℕ} (f : x ⟶ ⦋n + 1⦌) [Mono f]
    (j : Fin (n + 2)) (hj : ∀ t, f.toOrderHom t ≠ j) (r : Fin (n + 1))
    (hr : j.succAbove r ∉ Set.range f.toOrderHom) : x.len < n := by
  have : Mono (cofaceFactor f j) := cofaceFactor_mono f j hj
  apply lt_of_mono_omits (cofaceFactor f j) r
  intro t ht
  exact (cofaceFactor_omits_iff f j hj r).mp hr ⟨t, ht⟩

/-- Every original selected face has exactly one residual selected index. -/
theorem card_lowerFaces {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    (lowerFaces J j).card = J.card := by
  have h := congrArg Finset.card (image_lowerFaces J j hj)
  rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h
  exact h

@[simp]
theorem lowerFaces_erase {n : ℕ} (j : Fin (n + 2)) :
    lowerFaces (Finset.univ.erase j) j = Finset.univ := by
  ext r
  simp [lowerFaces, Fin.succAbove_ne]

/-- Adding any other original face adds its exact original residual face index. -/
@[simp]
theorem lowerFaces_insert_succAbove {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (r : Fin (n + 1)) : lowerFaces (insert (j.succAbove r) J) j = insert r (lowerFaces J j) := by
  ext s
  simp [lowerFaces]

end SimplexCategory.FaceSubdivision

end
end

section



/-! # Original face subdivision in the actual opposite-simplex matching source -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MorphismProperty Opposite Simplicial
open SimplexCategory.FaceSubdivision

namespace SimplexCategory.PartialMatching.FaceSubdivision

/-- Original omitted vertices remain omitted under every original matching comparison. -/
theorem misses_comparison {n : ℕ} {a b : reedyOp.Matching (op ⦋n⦌)} (f : a ⟶ b)
    (j : Fin (n + 1)) (h : j ∉ Set.range (reedyOp.matchingArrow a).unop.toOrderHom) :
    j ∉ Set.range (reedyOp.matchingArrow b).unop.toOrderHom := by
  intro hb
  obtain ⟨t, ht⟩ := hb
  apply h
  refine ⟨(reedyOp.matchingComparison f).unop.toOrderHom t, ?_⟩
  have htriangle := congrArg Quiver.Hom.unop (reedyOp.matchingArrow_comparison f)
  have happly := SimplexCategory.congr_toOrderHom_apply htriangle t
  change (reedyOp.matchingArrow a).unop.toOrderHom
    ((reedyOp.matchingComparison f).unop.toOrderHom t) =
    (reedyOp.matchingArrow b).unop.toOrderHom t at happly
  exact happly.trans ht

/-- The exact selected original face condition is closed under its original outgoing comparisons. -/
theorem faces_comparison {n : ℕ} {J : Finset (Fin (n + 1))}
    {a b : reedyOp.Matching (op ⦋n⦌)} (f : a ⟶ b) (h : Faces n J a) : Faces n J b := by
  obtain ⟨j, hj, hmiss⟩ := h
  exact ⟨j, hj, misses_comparison f j hmiss⟩

/-- An original comparison and its original inverse triangle give the same actual matching morphism.
-/
def matchingHomMk {n : ℕ} {a b : reedyOp.Matching (op ⦋n⦌)}
    (f : reedyOp.matchingTarget a ⟶ reedyOp.matchingTarget b) (hf : Mono f.unop)
    (h : reedyOp.matchingArrow a ≫ f = reedyOp.matchingArrow b) : a ⟶ b :=
  ObjectProperty.homMk (Under.homMk ⟨f, (reedyOp_inverse _).2 hf⟩ (by
    apply WideSubcategory.hom_ext
    exact h))

@[simp]
theorem matchingComparison_homMk {n : ℕ} {a b : reedyOp.Matching (op ⦋n⦌)}
    (f : reedyOp.matchingTarget a ⟶ reedyOp.matchingTarget b) (hf : Mono f.unop)
    (h : reedyOp.matchingArrow a ≫ f = reedyOp.matchingArrow b) :
    reedyOp.matchingComparison (matchingHomMk f hf h) = f := rfl

/-- The full selected subcategory retains the same original matching morphism. -/
def homMk {n : ℕ} {J : Finset (Fin (n + 1))} {a b : Index n J}
    (f : target a ⟶ target b) (hf : Mono f.unop) (h : arrow a ≫ f = arrow b) : a ⟶ b :=
  ObjectProperty.homMk (matchingHomMk f hf h)

@[simp]
theorem comparison_homMk {n : ℕ} {J : Finset (Fin (n + 1))} {a b : Index n J}
    (f : target a ⟶ target b) (hf : Mono f.unop) (h : arrow a ≫ f = arrow b) :
    comparison (homMk f hf h) = f := rfl

/-- Every comparison in the actual original matching source is determined by its original arrow. -/
theorem matching_hom_ext {n : ℕ} {a b : reedyOp.Matching (op ⦋n⦌)} (f g : a ⟶ b)
    (h : reedyOp.matchingComparison f = reedyOp.matchingComparison g) : f = g := by
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply WideSubcategory.hom_ext
  exact h

/-- The actual proper-mono matching source has at most one original comparison triangle. -/
instance matchingHomSubsingleton (n : ℕ) (a b : reedyOp.Matching (op ⦋n⦌)) : Subsingleton (a ⟶ b) :=
  ⟨fun f g => by
    apply matching_hom_ext
    apply Quiver.Hom.unop_inj
    have : Mono (reedyOp.matchingArrow a).unop := (reedyOp_inverse _).1 a.obj.hom.property
    apply (cancel_mono (reedyOp.matchingArrow a).unop).mp
    exact (congrArg Quiver.Hom.unop (reedyOp.matchingArrow_comparison f)).trans
      (congrArg Quiver.Hom.unop (reedyOp.matchingArrow_comparison g)).symm⟩

/-- The selected full original face category retains uniqueness of its original triangles. -/
instance indexHomSubsingleton (n : ℕ) (J : Finset (Fin (n + 1))) (a b : Index n J) :
    Subsingleton (a ⟶ b) :=
  ⟨fun f g => ObjectProperty.hom_ext (Faces n J) (Subsingleton.elim f.hom g.hom)⟩

/-- The original lower face is composed with the original supplied upper coface. -/
abbrev lowerToUpperObj {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a : Index n (lowerFaces J j)) : Index (n + 1) J := by
  have hm : Mono ((SimplexCategory.δ j).op ≫ arrow a).unop := by
    change Mono ((arrow a).unop ≫ SimplexCategory.δ j)
    infer_instance
  let b := reedyOp.matchingMk ((SimplexCategory.δ j).op ≫ arrow a)
    ((reedyOp_inverse _).2 hm) ((target_lt a).trans (Nat.lt_succ_self n))
  refine ⟨b, ?_⟩
  obtain ⟨r, hr, hmiss⟩ := a.property
  refine ⟨j.succAbove r, (mem_lowerFaces J j r).mp hr, ?_⟩
  intro hmem
  obtain ⟨t, ht⟩ := hmem
  change j.succAbove ((arrow a).unop.toOrderHom t) = j.succAbove r at ht
  exact hmiss ⟨t, Fin.succAbove_right_injective ht⟩

@[simp]
theorem target_lowerToUpperObj {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a : Index n (lowerFaces J j)) : target (lowerToUpperObj J j a) = target a := rfl

@[simp]
theorem arrow_lowerToUpperObj {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a : Index n (lowerFaces J j)) :
    arrow (lowerToUpperObj J j a) = (SimplexCategory.δ j).op ≫ arrow a := rfl

/-- The whole original lower-to-upper inclusion retains all original comparison triangles. -/
abbrev lowerToUpper {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    Index n (lowerFaces J j) ⥤ Index (n + 1) J where
  obj a := lowerToUpperObj J j a
  map {a b} f := homMk (a := lowerToUpperObj J j a) (b := lowerToUpperObj J j b)
    (@comparison n (lowerFaces J j) a b f)
    ((reedyOp_inverse _).1 f.hom.hom.right.property) (by
      change ((SimplexCategory.δ j).op ≫ arrow _) ≫ comparison f =
        (SimplexCategory.δ j).op ≫ arrow _
      rw [Category.assoc, arrow_comparison])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem comparison_lowerToUpper {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    {a b : Index n (lowerFaces J j)} (f : a ⟶ b) :
    comparison ((lowerToUpper J j).map f) = @comparison n (lowerFaces J j) a b f := rfl

/-- Every lower-to-upper original mono also omits the supplied new coface vertex. -/
theorem lowerToUpper_misses {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a : Index n (lowerFaces J j)) : j ∉ Set.range (arrow (lowerToUpperObj J j a)).unop.toOrderHom
        := by
  rintro ⟨t, ht⟩
  change j.succAbove ((arrow a).unop.toOrderHom t) = j at ht
  exact Fin.succAbove_ne _ _ ht

/-- The actual residual coefficient arrow from the original new face. -/
abbrev factorArrow {n : ℕ} {J : Finset (Fin (n + 2))} (a : Index (n + 1) J)
    (j : Fin (n + 2)) : op ⦋n⦌ ⟶ target a := (cofaceFactor (arrow a).unop j).op

/-- The residual retains the complete original new-face comparison triangle. -/
theorem factorArrow_spec {n : ℕ} {J : Finset (Fin (n + 2))} (a : Index (n + 1) J)
    (j : Fin (n + 2)) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    (SimplexCategory.δ j).op ≫ factorArrow a j = arrow a := by
  apply Quiver.Hom.unop_inj
  exact cofaceFactor_spec (arrow a).unop j (fun t ht => hmiss ⟨t, ht⟩)

/-- Every actual residual coefficient arrow is still an original inverse simplex map. -/
theorem factorArrow_mono {n : ℕ} {J : Finset (Fin (n + 2))} (a : Index (n + 1) J)
    (j : Fin (n + 2)) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    Mono (factorArrow a j).unop :=
  cofaceFactor_mono (arrow a).unop j (fun t ht => hmiss ⟨t, ht⟩)

/-- All original matching comparisons preserve the same actual residual comparison equation. -/
theorem factorArrow_comparison {n : ℕ} {J : Finset (Fin (n + 2))} {a b : Index (n + 1) J}
    (f : a ⟶ b) (j : Fin (n + 2)) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    factorArrow a j ≫ comparison f = factorArrow b j := by
  apply Quiver.Hom.unop_inj
  change (comparison f).unop ≫ cofaceFactor (arrow a).unop j = cofaceFactor (arrow b).unop j
  rw [comp_cofaceFactor (arrow a).unop j (fun t ht => hmiss ⟨t, ht⟩)]
  congr 1
  exact congrArg Quiver.Hom.unop (arrow_comparison f)

/-- The original coface is the actual initial source of every face omitting its vertex. -/
def faceTo {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∈ J)
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    faceMk J j hj ⟶ a :=
  homMk (a := faceMk J j hj) (b := a) (factorArrow a j) (factorArrow_mono a j hmiss)
    (factorArrow_spec a j hmiss)

@[simp]
theorem comparison_faceTo {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∈ J)
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    comparison (faceTo J j hj a hmiss) = factorArrow a j := rfl

/-- The original overlap mono gives its actual lower partial matching object. -/
abbrev residualObj {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    Index n (lowerFaces J j) := by
  have hbound : (target a).unop.len < n := by
    obtain ⟨k, hk, hkMiss⟩ := a.property
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    have hkr : k ∈ Set.range j.succAbove := by rw [Fin.range_succAbove]; exact hkj
    obtain ⟨r, hr⟩ := hkr
    have hmissing : j.succAbove r ∉ Set.range (arrow a).unop.toOrderHom := by
      simpa only [arrow, hr] using hkMiss
    exact cofaceFactor_lt (arrow a).unop j (fun t ht => hmiss ⟨t, ht⟩) r hmissing
  have hm : Mono (factorArrow a j).unop := factorArrow_mono a j hmiss
  let b := reedyOp.matchingMk (factorArrow a j) ((reedyOp_inverse _).2 hm) hbound
  refine ⟨b, ?_⟩
  obtain ⟨k, hk, hkMiss⟩ := a.property
  have hkj : k ≠ j := fun h => hj (h ▸ hk)
  have hkr : k ∈ Set.range j.succAbove := by rw [Fin.range_succAbove]; exact hkj
  obtain ⟨r, hr⟩ := hkr
  have hmissing : j.succAbove r ∉ Set.range (arrow a).unop.toOrderHom := by
    simpa only [arrow, hr] using hkMiss
  refine ⟨r, (mem_lowerFaces J j r).mpr (hr ▸ hk), ?_⟩
  change r ∉ Set.range (cofaceFactor (arrow a).unop j).toOrderHom
  exact (cofaceFactor_omits_iff (arrow a).unop j (fun t ht => hmiss ⟨t, ht⟩) r).mp hmissing

@[simp]
theorem target_residualObj {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    target (residualObj J j hj a hmiss) = target a := rfl

@[simp]
theorem arrow_residualObj {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    arrow (residualObj J j hj a hmiss) = factorArrow a j := rfl

/-- The genuine original overlap of the old selected faces and the new face. -/
def OverlapProperty {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    ObjectProperty (Index (n + 1) J) := fun a => j ∉ Set.range (arrow a).unop.toOrderHom

/-- The full selected face-matching subcategory whose simplex maps also omit vertex `j`. -/
abbrev Overlap {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :=
  (OverlapProperty J j).FullSubcategory

instance overlapHomSubsingleton {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a b : Overlap J j) : Subsingleton (a ⟶ b) :=
  ⟨fun f g => ObjectProperty.hom_ext (OverlapProperty J j) (Subsingleton.elim f.hom g.hom)⟩

/-- The original intersection functor retains each actual lower target and comparison. -/
def overlapToLower {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    Overlap J j ⥤ Index n (lowerFaces J j) where
  obj a := residualObj J j hj a.obj a.property
  map {a b} f := homMk
    (a := residualObj J j hj a.obj a.property) (b := residualObj J j hj b.obj b.property)
    (@comparison (n + 1) J a.obj b.obj f.hom) ((reedyOp_inverse _).1 f.hom.hom.hom.right.property)
    (factorArrow_comparison f.hom j a.property)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The original lower matching object is inserted as the same actual overlap object. -/
def lowerToOverlap {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    Index n (lowerFaces J j) ⥤ Overlap J j where
  obj a := ⟨lowerToUpperObj J j a, lowerToUpper_misses J j a⟩
  map {a b} f := by
    refine ObjectProperty.homMk ?_
    exact (lowerToUpper J j).map (X := a) (Y := b) f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original lower face arrow is recovered from the actual upper composite. -/
theorem factorArrow_lowerToUpper {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a : Index n (lowerFaces J j)) : factorArrow (lowerToUpperObj J j a) j = arrow a := by
  apply Quiver.Hom.unop_inj
  symm
  apply cofaceFactor_unique ((SimplexCategory.δ j).op ≫ arrow a).unop j
    (fun t ht => lowerToUpper_misses J j a ⟨t, ht⟩)
  rfl

/-- The original lower matching object is recovered by its actual upper coface residual. -/
theorem residual_lowerToUpper {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (a : Index n (lowerFaces J j)) :
    residualObj J j hj (lowerToUpperObj J j a) (lowerToUpper_misses J j a) = a := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  refine StructuredArrow.obj_ext _ _ rfl ?_
  apply WideSubcategory.hom_ext
  change factorArrow (lowerToUpperObj J j a) j ≫ 𝟙 (target a) = arrow a
  erw [Category.comp_id]
  exact factorArrow_lowerToUpper J j a

/-- The original upper overlap object is recovered by its actual lower coface residual. -/
theorem lowerToUpper_residual {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    lowerToUpperObj J j (residualObj J j hj a hmiss) = a := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  refine StructuredArrow.obj_ext _ _ rfl ?_
  apply WideSubcategory.hom_ext
  change ((SimplexCategory.δ j).op ≫ factorArrow a j) ≫ 𝟙 (target a) = arrow a
  rw [Category.comp_id, factorArrow_spec a j hmiss]

/-- The actual original upper overlap is recovered with its unchanged original underlying object. -/
theorem lowerToOverlap_overlapToLower {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (hj : j ∉ J) (a : Overlap J j) :
    (lowerToOverlap J j).obj ((overlapToLower J j hj).obj a) = a := by
  apply ObjectProperty.FullSubcategory.ext
  exact lowerToUpper_residual J j hj a.obj a.property

/-- The actual old/new face intersection is the genuine original lower partial matching category. -/
def overlapEquivalence {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    Overlap J j ≌ Index n (lowerFaces J j) where
  functor := overlapToLower J j hj
  inverse := lowerToOverlap J j
  unitIso := NatIso.ofComponents
    (fun a => eqToIso (lowerToOverlap_overlapToLower J j hj a).symm)
    (fun {_ _} _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun a => eqToIso (residual_lowerToUpper J j hj a))
    (fun {_ _} _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end SimplexCategory.PartialMatching.FaceSubdivision

end
end
end

section



/-! # Actual add-one original face matching pullback -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open SimplexCategory.PartialMatching
open SimplexCategory.PartialMatching.FaceSubdivision
open SimplexCategory.FaceSubdivision

namespace HomotopicalAlgebra.PartialFaceMatching.AddOne

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- The actual original old-face cone on the actual lower intersection. -/
def restrictionCone (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) : Cone (diagram B n (lowerFaces J j)) where
  pt := object B (n + 1) J
  π.app a := limit.π (diagram B (n + 1) J) (lowerToUpperObj J j a)
  π.naturality a b f := by
    change 𝟙 _ ≫ limit.π (diagram B (n + 1) J) (lowerToUpperObj J j b) =
      limit.π (diagram B (n + 1) J) (lowerToUpperObj J j a) ≫
        B.map (@comparison n (lowerFaces J j) a b f)
    rw [Category.id_comp]
    exact (limit.w (diagram B (n + 1) J) ((lowerToUpper J j).map (X := a) (Y := b) f)).symm

/-- The original old-to-intersection restriction on the actual finite matching limits. -/
def restriction (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    object B (n + 1) J ⟶ object B n (lowerFaces J j) :=
  limit.lift _ (restrictionCone B J j)

@[reassoc]
theorem restriction_π (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (a : Index n (lowerFaces J j)) :
    restriction B J j ≫ limit.π (diagram B n (lowerFaces J j)) a =
      limit.π (diagram B (n + 1) J) (lowerToUpperObj J j a) := limit.lift_π _ a

/-- The actual old-face projection from the actual enlarged original matching object. -/
abbrev oldProjection (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    object B (n + 1) (insert j J) ⟶ object B (n + 1) J :=
  projection B (n + 1) (Finset.subset_insert j J)

/-- The actual coefficient projection onto the original new face. -/
abbrev newProjection (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    object B (n + 1) (insert j J) ⟶ B.obj (op ⦋n⦌) :=
  faceProjection B (insert j J) j (Finset.mem_insert_self j J)

/-- The original old/new restriction square commutes on every actual lower face. -/
theorem square (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    oldProjection B J j ≫ restriction B J j = newProjection B J j ≫ map B n (lowerFaces J j) := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, restriction_π, projection_π, Category.assoc, map_π]
  let b := (ofSubset (n + 1) (Finset.subset_insert j J)).obj (lowerToUpperObj J j a)
  have hmiss : j ∉ Set.range (arrow b).unop.toOrderHom := lowerToUpper_misses J j a
  have h := (limit.w (diagram B (n + 1) (insert j J))
    (faceTo (insert j J) j (Finset.mem_insert_self j J) b hmiss)).symm
  change limit.π (diagram B (n + 1) (insert j J)) b =
    limit.π (diagram B (n + 1) (insert j J)) (faceMk (insert j J) j (Finset.mem_insert_self j J)) ≫
      B.map (factorArrow (lowerToUpperObj J j a) j) at h
  rw [factorArrow_lowerToUpper] at h
  exact h

/-- The actual original new face is outside the old selected face category. -/
private theorem newFace_not_old {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    ¬ Faces (n + 1) J (faceMk (insert j J) j (Finset.mem_insert_self j J)).obj := by
  rintro ⟨r, hr, hmiss⟩
  change r ∉ Set.range j.succAbove at hmiss
  rw [Fin.range_succAbove] at hmiss
  have hrj : r = j := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hmiss
  exact hj (hrj ▸ hr)

/-- A newly retained original face outside the old family omits the supplied vertex. -/
private theorem newOnly_misses {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (a : Index (n + 1) (insert j J)) (ha : ¬ Faces (n + 1) J a.obj) :
    j ∉ Set.range (arrow a).unop.toOrderHom := by
  obtain ⟨r, hr, hmiss⟩ := a.property
  obtain h | h := Finset.mem_insert.mp hr
  · subst r
    exact hmiss
  · exact (ha ⟨r, h, hmiss⟩).elim

/-- The old and new original cone legs agree on each actual original overlap face. -/
private theorem overlap_leg (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j)))
    (a : Index (n + 1) J) (hmiss : j ∉ Set.range (arrow a).unop.toOrderHom) :
    s.fst ≫ limit.π (diagram B (n + 1) J) a = s.snd ≫ B.map (factorArrow a j) := by
  have h := congrArg (fun f => f ≫ limit.π (diagram B n (lowerFaces J j))
    (residualObj J j hj a hmiss)) s.condition
  erw [Category.assoc, restriction_π, Category.assoc, map_π] at h
  let b := lowerToUpperObj J j (residualObj J j hj a hmiss)
  have htriangle : arrow b ≫ 𝟙 (target a) = arrow a := by
    change ((SimplexCategory.δ j).op ≫ factorArrow a j) ≫ 𝟙 (target a) = arrow a
    erw [Category.comp_id]
    exact factorArrow_spec a j hmiss
  let g : b ⟶ a := homMk (a := b) (b := a) (𝟙 (target a)) (by
    change Mono (𝟙 (target a).unop)
    infer_instance) htriangle
  have hπ := limit.w (diagram B (n + 1) J) g
  change limit.π (diagram B (n + 1) J) b ≫ B.map (𝟙 (target a)) =
    limit.π (diagram B (n + 1) J) a at hπ
  erw [B.map_id, Category.comp_id] at hπ
  erw [hπ] at h
  exact h

/-- The actual original cone leg obtained from the two compatible original cone families. -/
private def glueApp (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j)))
    (a : Index (n + 1) (insert j J)) : s.pt ⟶ B.obj (target a) := by
  classical
  exact if h : Faces (n + 1) J a.obj then
    s.fst ≫ limit.π (diagram B (n + 1) J) ⟨a.obj, h⟩
  else s.snd ≫ B.map (factorArrow a j)

private theorem glueApp_old (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j)))
    (a : Index (n + 1) (insert j J)) (ha : Faces (n + 1) J a.obj) :
    glueApp B J j s a = s.fst ≫ limit.π (diagram B (n + 1) J) ⟨a.obj, ha⟩ := by
  simp only [glueApp, dite_eq_left ha]

private theorem glueApp_new (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j)))
    (a : Index (n + 1) (insert j J)) (ha : ¬ Faces (n + 1) J a.obj) :
    glueApp B J j s a = s.snd ≫ B.map (factorArrow a j) := by
  simp only [glueApp, dite_eq_right ha]

/-- All actual original comparison triangles give the actual glued cone naturality. -/
private theorem glueApp_naturality (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j)))
    {a b : Index (n + 1) (insert j J)} (f : a ⟶ b) :
    glueApp B J j s a ≫ B.map (@comparison (n + 1) (insert j J) a b f) = glueApp B J j s b := by
  classical
  by_cases ha : Faces (n + 1) J a.obj
  · have hb := faces_comparison f.hom ha
    rw [glueApp_old B J j s a ha, glueApp_old B J j s b hb, Category.assoc]
    let g : (⟨a.obj, ha⟩ : Index (n + 1) J) ⟶ ⟨b.obj, hb⟩ := ObjectProperty.homMk f.hom
    exact congrArg (fun t => s.fst ≫ t) (limit.w (diagram B (n + 1) J) g)
  · have hma := newOnly_misses J j a ha
    have hmb := misses_comparison f.hom j hma
    by_cases hb : Faces (n + 1) J b.obj
    · rw [glueApp_new B J j s a ha, glueApp_old B J j s b hb]
      have h := overlap_leg B J j hj s ⟨b.obj, hb⟩ hmb
      change s.fst ≫ limit.π (diagram B (n + 1) J) ⟨b.obj, hb⟩ =
        s.snd ≫ B.map (factorArrow b j) at h
      rw [h, Category.assoc, ← B.map_comp]
      exact congrArg (fun t => s.snd ≫ B.map t) (factorArrow_comparison f j hma)
    · rw [glueApp_new B J j s a ha, glueApp_new B J j s b hb, Category.assoc, ← B.map_comp]
      exact congrArg (fun t => s.snd ≫ B.map t) (factorArrow_comparison f j hma)

/-- The compatible original old-face and new-face cones produce the actual enlarged matching cone.
-/
private def glueCone (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j))) :
    Cone (diagram B (n + 1) (insert j J)) where
  pt := s.pt
  π.app a := glueApp B J j s a
  π.naturality a b f := by
    change 𝟙 _ ≫ glueApp B J j s b =
      glueApp B J j s a ≫ B.map (@comparison (n + 1) (insert j J) a b f)
    rw [Category.id_comp]
    exact (glueApp_naturality B J j hj s f).symm

/-- The actual enlarged finite matching limit supplies every original compatible pullback lift. -/
private def glueLift (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j))) :
    s.pt ⟶ object B (n + 1) (insert j J) := limit.lift _ (glueCone B J j hj s)

private theorem glueLift_old (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j))) :
    glueLift B J j hj s ≫ oldProjection B J j = s.fst := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, projection_π, limit.lift_π]
  exact glueApp_old B J j s ((ofSubset (n + 1) (Finset.subset_insert j J)).obj a) a.property

private theorem factorArrow_newFace {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    factorArrow (faceMk (insert j J) j (Finset.mem_insert_self j J)) j = 𝟙 (op ⦋n⦌) := by
  apply Quiver.Hom.unop_inj
  exact cofaceFactor_coface j

private theorem glueLift_new (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j))) :
    glueLift B J j hj s ≫ newProjection B J j = s.snd := by
  erw [limit.lift_π]
  change glueApp B J j s (faceMk (insert j J) j (Finset.mem_insert_self j J)) = s.snd
  erw [glueApp_new B J j s _ (newFace_not_old J j hj), factorArrow_newFace, B.map_id,
      Category.comp_id]

private theorem glueLift_unique (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (s : PullbackCone (restriction B J j) (map B n (lowerFaces J j)))
    (m : s.pt ⟶ object B (n + 1) (insert j J))
    (hOld : m ≫ oldProjection B J j = s.fst) (hNew : m ≫ newProjection B J j = s.snd) :
    m = glueLift B J j hj s := by
  classical
  apply limit.hom_ext
  intro a
  erw [limit.lift_π]
  change m ≫ limit.π (diagram B (n + 1) (insert j J)) a = glueApp B J j s a
  by_cases ha : Faces (n + 1) J a.obj
  · rw [glueApp_old B J j s a ha]
    have h := congrArg (fun t => t ≫ limit.π (diagram B (n + 1) J) ⟨a.obj, ha⟩) hOld
    erw [Category.assoc, projection_π] at h
    exact h
  · rw [glueApp_new B J j s a ha]
    have w := limit.w (diagram B (n + 1) (insert j J))
      (faceTo (insert j J) j (Finset.mem_insert_self j J) a (newOnly_misses J j a ha))
    change newProjection B J j ≫ B.map (factorArrow a j) =
      limit.π (diagram B (n + 1) (insert j J)) a at w
    rw [← w, ← Category.assoc, hNew]

/-- The exact original add-one face cone is a limit pullback cone. -/
private def rawIsLimit (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    IsLimit (PullbackCone.mk (oldProjection B J j) (newProjection B J j) (square B J j)) :=
  PullbackCone.IsLimit.mk (square B J j) (glueLift B J j hj)
    (glueLift_old B J j hj) (glueLift_new B J j hj) (glueLift_unique B J j hj)

/-- Adding the original face is the actual pullback over its original lower partial matching object.
-/
theorem isPullback (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    IsPullback (oldProjection B J j) (newProjection B J j) (restriction B J j)
      (map B n (lowerFaces J j)) := IsPullback.of_isLimit (rawIsLimit B J j hj)

/-- The exact constructed pullback proof supplies the actual original limit cone. -/
def isLimit (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J) :
    IsLimit (PullbackCone.mk (oldProjection B J j) (newProjection B J j) (square B J j)) :=
  (isPullback B J j hj).isLimit

/-- Every original coefficient transformation preserves the actual old-face projection. -/
@[reassoc]
theorem oldProjection_naturality {B B' : SimplicialObject C} (f : B ⟶ B') {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    limMap (transformation f (n + 1) (insert j J)) ≫ oldProjection B' J j =
      oldProjection B J j ≫ limMap (transformation f (n + 1) J) := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, projection_π, limMap_π, Category.assoc, limMap_π,
    ← Category.assoc, projection_π]
  rfl

/-- Every original coefficient transformation preserves the actual new coface projection. -/
@[reassoc]
theorem newProjection_naturality {B B' : SimplicialObject C} (f : B ⟶ B') {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    limMap (transformation f (n + 1) (insert j J)) ≫ newProjection B' J j =
      newProjection B J j ≫ f.app (op ⦋n⦌) :=
  limMap_π (transformation f (n + 1) (insert j J))
      (faceMk (insert j J) j (Finset.mem_insert_self j J))

/-- Every original coefficient transformation preserves the actual lower intersection restriction.
-/
@[reassoc]
theorem restriction_naturality {B B' : SimplicialObject C} (f : B ⟶ B') {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    limMap (transformation f (n + 1) J) ≫ restriction B' J j =
      restriction B J j ≫ limMap (transformation f n (lowerFaces J j)) := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, restriction_π, limMap_π, Category.assoc, limMap_π,
    ← Category.assoc, restriction_π]
  rfl

/-- The original complete matching maps retain their actual lower-coface restriction equation. -/
@[reassoc]
theorem map_restriction (B : SimplicialObject C) {n : ℕ}
    (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    map B (n + 1) J ≫ restriction B J j = B.δ j ≫ map B n (lowerFaces J j) := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, restriction_π, map_π, Category.assoc, map_π]
  change B.map ((SimplexCategory.δ j).op ≫ arrow a) = B.map (SimplexCategory.δ j).op ≫ B.map
      (arrow a)
  exact B.map_comp _ _

private theorem singleton_misses {n : ℕ} (j : Fin (n + 2)) (a : Index (n + 1) {j}) :
    j ∉ Set.range (arrow a).unop.toOrderHom := by
  obtain ⟨r, hr, hmiss⟩ := a.property
  have hrj : r = j := Finset.mem_singleton.mp hr
  subst r
  exact hmiss

private def singletonCone (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    Cone (diagram B (n + 1) {j}) where
  pt := B.obj (op ⦋n⦌)
  π.app a := B.map (factorArrow a j)
  π.naturality a b f := by
    change 𝟙 _ ≫ B.map (factorArrow b j) =
      B.map (factorArrow a j) ≫ B.map (@comparison (n + 1) {j} a b f)
    erw [Category.id_comp, ← B.map_comp, factorArrow_comparison f j (singleton_misses j a)]

private def singletonInverse (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    B.obj (op ⦋n⦌) ⟶ object B (n + 1) {j} := limit.lift _ (singletonCone B j)

private theorem singletonInverse_projection (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    singletonInverse B j ≫ faceProjection B {j} j (Finset.mem_singleton_self j) = 𝟙 _ := by
  erw [limit.lift_π]
  change B.map (factorArrow (faceMk {j} j (Finset.mem_singleton_self j)) j) = 𝟙 _
  have h : factorArrow (faceMk {j} j (Finset.mem_singleton_self j)) j = 𝟙 (op ⦋n⦌) := by
    apply Quiver.Hom.unop_inj
    exact cofaceFactor_coface j
  erw [h, B.map_id]

private theorem singletonProjection_inverse (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    faceProjection B {j} j (Finset.mem_singleton_self j) ≫ singletonInverse B j = 𝟙 _ := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, limit.lift_π, Category.id_comp]
  exact limit.w (diagram B (n + 1) {j})
    (faceTo {j} j (Finset.mem_singleton_self j) a (singleton_misses j a))

/-- The actual singleton-face matching projection is an original coefficient isomorphism. -/
instance singletonProjection_isIso (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    IsIso (faceProjection B {j} j (Finset.mem_singleton_self j)) :=
  ⟨⟨singletonInverse B j, singletonProjection_inverse B j, singletonInverse_projection B j⟩⟩

/-- The singleton-face finite matching limit has its actual original coefficient endpoint. -/
def singletonIso (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    object B (n + 1) {j} ≅ B.obj (op ⦋n⦌) := asIso
        (faceProjection B {j} j (Finset.mem_singleton_self j))

/-- The singleton isomorphism retains its original matching projection. -/
theorem singletonIso_hom (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    (singletonIso B j).hom = faceProjection B {j} j (Finset.mem_singleton_self j) := rfl

/-- The singleton original matching map reads back the same original simplicial coface. -/
@[reassoc]
theorem map_singletonIso_hom (B : SimplicialObject C) {n : ℕ} (j : Fin (n + 2)) :
    map B (n + 1) {j} ≫ (singletonIso B j).hom = B.δ j :=
  map_faceProjection B {j} j (Finset.mem_singleton_self j)

end HomotopicalAlgebra.PartialFaceMatching.AddOne

end
end
end

section



/-! # Original finite partial matching restriction identities and compositions -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.PartialFaceMatching

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- Restriction to the same original selected-face family is the original identity. -/
theorem projection_self (B : SimplicialObject C) (n : ℕ) (J : Finset (Fin (n + 1))) (h : J ⊆ J) :
    projection B n h = 𝟙 (object B n J) := by
  apply limit.hom_ext
  intro a
  rw [projection_π, Category.id_comp]
  rfl

/-- Every original finite face-family restriction retains its complete original composition. -/
@[reassoc]
theorem projection_comp (B : SimplicialObject C) (n : ℕ) {J K L : Finset (Fin (n + 1))}
    (hJK : J ⊆ K) (hKL : K ⊆ L) :
    projection B n hKL ≫ projection B n hJK = projection B n (hJK.trans hKL) := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, projection_π, projection_π]
  exact projection_π B n hKL ((SimplexCategory.PartialMatching.ofSubset n hJK).obj a)

end HomotopicalAlgebra.PartialFaceMatching

end
end
end

section



/-!
# Actual finite partial-face restriction classes from lower original matching maps

Finite insertions use the original add-one pullback and ordinary scalar
base-change/composition laws. Identity and composition are the exact original
restriction maps. No class closure under arbitrary limits is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open SimplexCategory.FaceSubdivision

namespace HomotopicalAlgebra.PartialFaceMatching

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- Equality of original selected target families transports the whole original restriction
predicate. -/
theorem projection_mem_congr (P : MorphismProperty C) (B : SimplicialObject C) (n : ℕ)
    {J K L : Finset (Fin (n + 1))} (he : K = L) (hJK : J ⊆ K) (hJL : J ⊆ L) :
    P (projection B n hJK) ↔ P (projection B n hJL) := by
  subst L
  rfl

/-- The actual original add-one face projection retains any ordinary base-change stable source
class. -/
theorem oldProjection_mem (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    (B : SimplicialObject C) {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ J)
    (hmap : P (map B n (lowerFaces J j))) : P (AddOne.oldProjection B J j) :=
  P.of_isPullback (AddOne.isPullback B J j hj).flip hmap

/-- Every original finite restriction retains a source class when all original lower matching maps
do. -/
theorem projection_mem_of_lower (P : MorphismProperty C) [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (B : SimplicialObject C) (n : ℕ)
    (hmap : ∀ J : Finset (Fin (n + 1)), P (map B n J))
    {J K : Finset (Fin (n + 2))} (hJK : J ⊆ K) : P (projection B (n + 1) hJK) := by
  have H : ∀ D : Finset (Fin (n + 2)), P
      (projection B (n + 1) (Finset.subset_union_right (s₁ := D) (s₂ := J))) := by
    intro D
    induction D using Finset.induction with
    | empty =>
      apply (projection_mem_congr P B (n + 1) (Finset.empty_union J) _ (Finset.Subset.refl J)).2
      rw [projection_self]
      exact P.id_mem _
    | @insert j D hj ih =>
      by_cases hju : j ∈ D ∪ J
      · have he : insert j D ∪ J = D ∪ J := by simp [Finset.insert_union, hju]
        exact (projection_mem_congr P B (n + 1) he _ _).2 ih
      · have hOld : P (AddOne.oldProjection B (D ∪ J) j) :=
          oldProjection_mem P B (D ∪ J) j hju (hmap _)
        have hcomp := P.comp_mem _ _ hOld ih
        have he : insert j D ∪ J = insert j (D ∪ J) := Finset.insert_union j D J
        have hc : P (projection B (n + 1)
            ((Finset.subset_union_right (s₁ := D) (s₂ := J)).trans
                (Finset.subset_insert j (D ∪ J)))) := by
          rw [← projection_comp]
          exact hcomp
        exact (projection_mem_congr P B (n + 1) he _ _).2 hc
  have he : (K \ J) ∪ J = K := Finset.sdiff_union_of_subset hJK
  have h := H (K \ J)
  exact (projection_mem_congr P B (n + 1) he _ hJK).1 h

/-- The original lower face family is nonempty when the original old family is nonempty. -/
theorem lowerFaces_nonempty {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (hj : j ∉ J) (hJ : J.Nonempty) : (lowerFaces J j).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_lowerFaces J j hj]
  exact Finset.card_pos.mpr hJ

/-- A proper original face insertion has a proper original lower intersection family. -/
theorem lowerFaces_ne_univ {n : ℕ} (J : Finset (Fin (n + 2))) (j : Fin (n + 2))
    (hj : j ∉ J) (hJ : insert j J ≠ Finset.univ) : lowerFaces J j ≠ Finset.univ := by
  intro h
  apply hJ
  rw [← Finset.card_eq_iff_eq_univ]
  rw [Finset.card_insert_of_notMem hj, ← card_lowerFaces J j hj, h]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Every original nonempty proper face restriction retains the source class from nonempty proper
lower
matching maps. -/
theorem projection_mem_of_lower_proper (P : MorphismProperty C) [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (B : SimplicialObject C) (n : ℕ)
    (hmap : ∀ L : Finset (Fin (n + 1)), L.Nonempty → L ≠ Finset.univ → P (map B n L))
    {J K : Finset (Fin (n + 2))} (hJK : J ⊆ K) (hJ : J.Nonempty) (hK : K ≠ Finset.univ) :
    P (projection B (n + 1) hJK) := by
  have H : ∀ D : Finset (Fin (n + 2)), (D ∪ J) ≠ Finset.univ →
      P (projection B (n + 1) (Finset.subset_union_right (s₁ := D) (s₂ := J))) := by
    intro D
    induction D using Finset.induction with
    | empty =>
      intro _
      apply (projection_mem_congr P B (n + 1) (Finset.empty_union J) _ (Finset.Subset.refl J)).2
      rw [projection_self]
      exact P.id_mem _
    | @insert j D hj ih =>
      intro hProper
      by_cases hju : j ∈ D ∪ J
      · have he : insert j D ∪ J = D ∪ J := by simp [Finset.insert_union, hju]
        have hp : D ∪ J ≠ Finset.univ := by simpa only [he] using hProper
        exact (projection_mem_congr P B (n + 1) he _ _).2 (ih hp)
      · have he : insert j D ∪ J = insert j (D ∪ J) := Finset.insert_union j D J
        have hp : insert j (D ∪ J) ≠ Finset.univ := by simpa only [he] using hProper
        have hOld : P (AddOne.oldProjection B (D ∪ J) j) :=
          oldProjection_mem P B (D ∪ J) j hju
            (hmap _ (lowerFaces_nonempty (D ∪ J) j hju
              (hJ.mono (Finset.subset_union_right))) (lowerFaces_ne_univ (D ∪ J) j hju hp))
        have hprev : D ∪ J ≠ Finset.univ := by
          intro hu
          exact hp (by simp [hu])
        have hcomp := P.comp_mem _ _ hOld (ih hprev)
        have hc : P (projection B (n + 1)
            ((Finset.subset_union_right (s₁ := D) (s₂ := J)).trans
                (Finset.subset_insert j (D ∪ J)))) := by
          rw [← projection_comp]
          exact hcomp
        exact (projection_mem_congr P B (n + 1) he _ _).2 hc
  have he : (K \ J) ∪ J = K := Finset.sdiff_union_of_subset hJK
  have hp : (K \ J) ∪ J ≠ Finset.univ := by simpa only [he] using hK
  exact (projection_mem_congr P B (n + 1) he _ hJK).1 (H (K \ J) hp)

end HomotopicalAlgebra.PartialFaceMatching

end
end
end

section



/-!
# Genuine partial matching classes of homotopically constant right frames

Dimension induction and finite face insertion use the actual original
pullback maps. All partial maps are fibrations; every nonempty proper face
family gives a trivial fibration. Weakness follows from the unchanged weak
coefficient face and the actual trivial projection to one original face.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.RightFrameHornGeometry

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- At original degree zero every actual partial matching object is terminal. -/
def zeroPartialMatchingIsTerminal (B : SimplicialObject C) (J : Finset (Fin 1)) :
    IsTerminal (PartialFaceMatching.object B 0 J) := by
  let _ : IsEmpty (SimplexCategory.PartialMatching.Index 0 J) := ⟨fun a => isEmptyElim a.obj⟩
  exact isLimitEquivIsTerminalOfIsEmpty C (limit.cone _) (limit.isLimit _)

/-- Actual original full matching fibrations and weak structure maps derive every partial matching
class. -/
theorem partialMatching_classes (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g)) :
    ∀ n : ℕ,
      (∀ J : Finset (Fin (n + 1)), fibrations C (PartialFaceMatching.map B n J)) ∧
      (∀ J : Finset (Fin (n + 1)), J.Nonempty → J ≠ Finset.univ →
        trivialFibrations C (PartialFaceMatching.map B n J)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro J
      have h := (isFibrant_iff_of_isTerminal (PartialFaceMatching.map B 0 J)
        (zeroPartialMatchingIsTerminal B J)).1 (degree_isFibrant B hB (op ⦋0⦌))
      exact (fibration_iff _).1 h
    · intro J hJ hProper
      obtain ⟨j, hj⟩ := hJ
      have hu : J = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        have he : i = j := Fin.ext
            ((Nat.lt_one_iff.mp i.isLt).trans (Nat.lt_one_iff.mp j.isLt).symm)
        exact he ▸ hj
      exact (hProper hu).elim
  | succ n ih =>
    have hf : ∀ J : Finset (Fin (n + 2)), fibrations C (PartialFaceMatching.map B (n + 1) J) := by
      intro J
      have hp := PartialFaceMatching.projection_mem_of_lower (fibrations C) B n ih.1
          (Finset.subset_univ J)
      rw [← PartialFaceMatching.map_projection B (n + 1) (Finset.subset_univ J)]
      exact (fibrations C).comp_mem _ _ (fullPartialMatching_fibration B hB (n + 1)) hp
    refine ⟨hf, ?_⟩
    intro J hJ hProper
    obtain ⟨j, hj⟩ := hJ
    have hs : ({j} : Finset (Fin (n + 2))) ⊆ J := Finset.singleton_subset_iff.mpr hj
    have hp := PartialFaceMatching.projection_mem_of_lower_proper (trivialFibrations C) B n ih.2 hs
      (Finset.singleton_nonempty j) hProper
    let q := PartialFaceMatching.projection B (n + 1) hs ≫
      (PartialFaceMatching.AddOne.singletonIso B j).hom
    have hq : trivialFibrations C q :=
      (trivialFibrations C).comp_mem _ _ hp ((trivialFibrations C).of_isIso _)
    have hcomp : PartialFaceMatching.map B (n + 1) J ≫ q = B.δ j := by
      dsimp only [q]
      rw [← Category.assoc, PartialFaceMatching.map_projection,
        PartialFaceMatching.AddOne.map_singletonIso_hom]
    refine ⟨hf J, ?_⟩
    apply (weakEquivalences C).of_postcomp (PartialFaceMatching.map B (n + 1) J) q hq.2
    rw [hcomp]
    exact hW (SimplexCategory.δ j).op

/-- Every original positive horn matching map is a genuine source trivial fibration. -/
theorem hornMatchingMap_trivialFibration (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2)) : trivialFibrations C (PartialFaceMatching.hornMap B (n + 1) k) := by
  have hNE : (Finset.univ.erase k : Finset (Fin (n + 2))).Nonempty := by
    obtain ⟨j, hj⟩ := exists_ne k
    exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
  have hProper : (Finset.univ.erase k : Finset (Fin (n + 2))) ≠ Finset.univ := by
    intro h
    have hk := Finset.mem_univ k
    rw [← h] at hk
    exact Finset.notMem_erase k _ hk
  exact (partialMatching_classes B hB hW (n + 1)).2 _ hNE hProper

end HomotopicalAlgebra.RightFrameHornGeometry

end
end
end

section



/-!
# The actual right-frame resolution Hom is a native Kan complex

The original full matching fibrations and weak structure maps derive the
actual horn matching trivial fibration. The original coefficient cofibration
from the initial object then gives a lift with every original horn face.
The same standard-simplex map fills the native simplicial-set horn.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.RightFrameHornGeometry

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The original coefficient horn map gives the complete source lifting square. -/
theorem coefficientHornSquare (X : C) (B : SimplicialObject C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    CommSq (initial.to (B.obj (op ⦋n + 1⦌))) (initial.to X)
      (PartialFaceMatching.hornMap B (n + 1) k) (hornHomMap X B (n + 1) k z) :=
  ⟨by simp⟩

/-- The actual C weak factorization system lifts the original square from cofibrant X. -/
theorem coefficientHornSquare_hasLift (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    (coefficientHornSquare X B n k z).HasLift := by
  let _ : HasLiftingProperty (initial.to X) (PartialFaceMatching.hornMap B (n + 1) k) :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (mem_cofibrations (initial.to X))
      (hornMatchingMap_trivialFibration B hB hW n k)
  infer_instance

/-- The actual source lift is the original coefficient simplex with the given entire horn. -/
def coefficientHornFiller (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    X ⟶ B.obj (op ⦋n + 1⦌) := by
  letI := coefficientHornSquare_hasLift X B hB hW n k z
  exact (coefficientHornSquare X B n k z).lift

/-- The coefficient filler has the complete original partial-matching factorization. -/
theorem coefficientHornFiller_fac (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    coefficientHornFiller X B hB hW n k z ≫ PartialFaceMatching.hornMap B (n + 1) k =
      hornHomMap X B (n + 1) k z := by
  let _ := coefficientHornSquare_hasLift X B hB hW n k z
  exact (coefficientHornSquare X B n k z).fac_right

/-- Every original proper mono face is retained by the actual coefficient filler. -/
theorem coefficientHornFiller_π (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (a : SimplexCategory.PartialMatching.HornIndex (n + 1) k) :
    coefficientHornFiller X B hB hW n k z ≫ B.map (SimplexCategory.PartialMatching.arrow a) =
      hornCoordinate X B (n + 1) k z a :=
  hornMatchingLift_π X B (n + 1) k z (coefficientHornFiller X B hB hW n k z)
    (coefficientHornFiller_fac X B hB hW n k z) a

/-- The coefficient filler is its actual full standard-simplex map in the original Hom complex. -/
def hornFiller (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    (Δ[n + 1] : SSet.{v}) ⟶ ResolutionHomComplex.right X B :=
  homSimplex X B (n + 1) (coefficientHornFiller X B hB hW n k z)

/-- The actual full standard simplex extends the original horn through its native inclusion. -/
theorem hornFiller_extension (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    (SSet.horn.{v} (n + 1) k).ι ≫ hornFiller X B hB hW n k z = z :=
  homSimplex_horn_extension X B n k z (coefficientHornFiller X B hB hW n k z)
    (coefficientHornFiller_fac X B hB hW n k z)

/-- In the actual model category, the original right resolution Hom is a native Kan complex. -/
theorem right_kanComplex (X : C) [IsCofibrant X] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g)) :
    SSet.KanComplex (ResolutionHomComplex.right X B) := by
  apply SSet.KanComplex.iff.mpr
  intro n k f hf
  refine ⟨hornFiller X B hB hW n k hf.desc, ?_⟩
  intro j hj
  calc
    SSet.stdSimplex.δ j ≫ hornFiller X B hB hW n k hf.desc =
        SSet.horn.ι k j hj ≫ ((SSet.horn (n + 1) k).ι ≫
          hornFiller X B hB hW n k hf.desc) := by rw [← Category.assoc, SSet.horn.ι_ι]
    _ = SSet.horn.ι k j hj ≫ hf.desc := by rw [hornFiller_extension]
    _ = f j hj := hf.ι_desc j hj

end HomotopicalAlgebra.RightFrameHornGeometry

end
end
end
