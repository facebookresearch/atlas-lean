/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicColimits
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# Original variable cell attachments and unchanged cellular arrows

Retain every original inner object, cell label, cofan, injection and endpoint map.
Greatest-inner joins use the actual stated empty cell cofans and original colimits.

The primary mathematical source is Mark Hovey, *Model Categories* (1999),
Lemma 2.1.12, printed p.31 / PDF p.41. The project uses original well-ordered
shapes, independent universes and explicitly supplied empty cofans and pushouts.
The source comparison and complete API scope are recorded in the adjacent README.md.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u v w w' t ν

namespace CategoryTheory.SmallObject.CellularNormalization

section EmptyAttachments

variable {C : Type u} [Category.{v} C]
variable {α : Type t} {A B : α → C} (g : ∀ a, A a ⟶ B a)

/-- A stated empty cofan identifies its actual point as initial. -/
def initialOfEmptyCofan {D : PEmpty.{ν + 1} → C} (c : Cofan D)
    (hc : IsColimit c) : IsInitial c.pt :=
  IsInitial.ofUniqueHom
    (fun X => hc.desc (Cofan.mk X (fun i => i.elim)))
    (fun _ _ => hc.hom_ext (fun i => i.as.elim))

/-- Every original isomorphism is the actual pushout of the stated empty cell cofans. -/
noncomputable def emptyAttachCells {X Y : C} (f : X ⟶ Y) [IsIso f]
    {D₁ D₂ : PEmpty.{ν + 1} → C} (c₁ : Cofan D₁) (c₂ : Cofan D₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) : AttachCells.{ν} g f := by
  let z₁ := initialOfEmptyCofan c₁ h₁
  let z₂ := initialOfEmptyCofan c₂ h₂
  let e : c₁.pt ≅ c₂.pt := z₁.uniqueUpToIso z₂
  exact
    { ι := PEmpty
      π i := i.elim
      cofan₁ := Cofan.mk c₁.pt (fun i : PEmpty.{ν + 1} => i.elim)
      cofan₂ := Cofan.mk c₂.pt (fun i : PEmpty.{ν + 1} => i.elim)
      isColimit₁ := (IsColimit.precomposeHomEquiv
          (Discrete.natIso (fun i : Discrete PEmpty => i.as.elim)) _).1
        (IsColimit.ofIsoColimit h₁ (Cocone.ext (Iso.refl _) (fun i => i.as.elim)))
      isColimit₂ := (IsColimit.precomposeHomEquiv
          (Discrete.natIso (fun i : Discrete PEmpty => i.as.elim)) _).1
        (IsColimit.ofIsoColimit h₂ (Cocone.ext (Iso.refl _) (fun i => i.as.elim)))
      m := e.hom
      hm i := i.elim
      g₁ := z₁.to X
      g₂ := z₂.to Y
      isPushout := IsPushout.of_vert_isIso (CommSq.mk (z₁.hom_ext _ _)) }

end EmptyAttachments

section OriginalSuccessors

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]

/-- The standard well-founded successor structure on the actual dependent lexicographic sum. -/
@[instance_reducible]
noncomputable def flatSuccOrder : SuccOrder (Index K) := by
  let _ : WellFoundedLT (Index K) := lexWellFounded (K := K)
  exact SuccOrder.ofLinearWellFoundedLT (Index K)

section

/-- The actual successor order of the original dependent lexicographic sum. -/
noncomputable local instance successorsSuccOrder : SuccOrder (Index K) := flatSuccOrder

omit [SuccOrder J] [OrderBot J] [∀ j, OrderBot (K j)] in
/-- A genuine original inner successor is literally the flattened successor. -/
theorem flat_succ_inner (j : J) (k : K j) (hk : ¬ IsMax k) :
    Order.succ (vertex j k) = vertex j (Order.succ k) :=
  Order.succ_eq_of_covBy (inner_covBy (K := K) hk)

omit [OrderBot J] [∀ j, SuccOrder (K j)] in
/-- Greatest-inner joins go to the next original outer bottom. -/
theorem flat_succ_join (j : J) (k : K j) (hj : ¬ IsMax j) (hk : IsMax k) :
    Order.succ (vertex j k) = vertex (Order.succ j) (⊥ : K (Order.succ j)) :=
  Order.succ_eq_of_covBy (join_covBy (K := K) hj hk)

end

variable (F : J ⥤ C)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (F.map (homOfLE (Order.le_succ j))))

omit [OrderBot J] [WellFoundedLT J] in
/-- The original greatest-inner endpoint leg is an isomorphism by its actual colimit. -/
theorem inner_endpoint_isIso (j : J) (k : K j) (hk : IsMax k) : IsIso ((c j).incl.app k) := by
  apply (c j).isColimit.isIso_ι_app_of_isTerminal
  refine IsTerminal.ofUniqueHom (fun i => homOfLE (by
      obtain h | h := le_total i k
      · exact h
      · exact hk h)) (fun i f => Subsingleton.elim _ _)

end OriginalSuccessors

section WholePresentations

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (outer.F.map (homOfLE (Order.le_succ j))))

local instance : WellFoundedLT (Index K) := lexWellFounded
/-- The actual lexicographic successor order used by the normalized presentation. -/
noncomputable local instance presentationSuccOrder : SuccOrder (Index K) := flatSuccOrder

/-- The single variable-inner presentation keeps the original source and endpoint arrow. -/
noncomputable def normalizedPresentation : TransfiniteCompositionOfShape (Index K) f where
  F := diagram outer.F c
  isoBot := (c ⊥).isoBot ≪≫ outer.isoBot
  isWellOrderContinuous := diagramIsWellOrderContinuous outer.F c
  incl := endpoint outer.F c outer.incl
  isColimit := endpointIsColimit outer.F c outer.incl outer.isColimit
  fac := by
    have hroot : innerRoot outer.F c (⊥ : J) (⊥ : K ⊥) = (c ⊥).isoBot.inv := by
      dsimp only [innerRoot]
      have h : homOfLE (bot_le : (⊥ : K ⊥) ≤ ⊥) = 𝟙 (⊥ : K ⊥) := Subsingleton.elim _ _
      rw [h, Functor.map_id, Category.comp_id]
    have hleg := innerRoot_endpoint_leg outer.F c outer.incl (⊥ : J) (⊥ : K ⊥)
    rw [hroot] at hleg
    have hf : (outer.isoBot.inv ≫ (c ⊥).isoBot.inv) ≫
        (endpoint outer.F c outer.incl).app (vertex (⊥ : J) (⊥ : K ⊥)) = f :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t => outer.isoBot.inv ≫ t) hleg).trans outer.fac)
    exact hf

/-- Every normalized endpoint leg is the actual composite of the original inner and outer legs. -/
theorem normalizedPresentation_incl (j : J) (k : K j) :
    (normalizedPresentation outer c).incl.app (vertex j k) =
      (c j).incl.app k ≫ outer.incl.app (Order.succ j) := rfl

/-- Every original outer vertex remains represented by its original inner root map. -/
@[reassoc]
theorem normalizedPresentation_root_leg (j : J) (k : K j) :
    innerRoot outer.F c j k ≫ (normalizedPresentation outer c).incl.app (vertex j k) =
      outer.incl.app j :=
  innerRoot_endpoint_leg outer.F c outer.incl j k

end WholePresentations

section OriginalCellMaps

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (outer.F.map (homOfLE (Order.le_succ j))))

local instance : WellFoundedLT (Index K) := lexWellFounded
/-- The actual lexicographic successor order used for original cell-map transport. -/
noncomputable local instance cellsSuccOrder : SuccOrder (Index K) := flatSuccOrder

variable (P : MorphismProperty C) [P.RespectsIso]

/-- The exact target equality gives the standard arrow comparison of two original diagram maps. -/
def diagramArrowIso {a b d : Index K} (hab : a ≤ b) (had : a ≤ d) (e : b = d) :
    Arrow.mk ((diagram outer.F c).map (homOfLE hab)) ≅
      Arrow.mk ((diagram outer.F c).map (homOfLE had)) :=
  Arrow.isoMk (Iso.refl _) ((diagram outer.F c).mapIso (eqToIso e)) (by
    change (𝟙 _) ≫ (diagram outer.F c).map (homOfLE had) =
      (diagram outer.F c).map (homOfLE hab) ≫ (diagram outer.F c).map (eqToHom e)
    exact (Category.id_comp _).trans
      ((congrArg (diagram outer.F c).map (Subsingleton.elim (homOfLE had)
        (homOfLE hab ≫ eqToHom e))).trans ((diagram outer.F c).map_comp _ _)))

/-- Every flat genuine successor comes from the original inner step or greatest-stage join. -/
theorem normalized_map_mem
    (hc : ∀ (j : J) (k : K j) (_ : ¬ IsMax k),
      P ((c j).F.map (homOfLE (Order.le_succ k))))
    (hjoin : ∀ (j : J) (k : K j) (hj : ¬ IsMax j) (_ : IsMax k),
      P (crossMap outer.F c (Order.lt_succ_iff_not_isMax.mpr hj) k (⊥ : K (Order.succ j))))
    (a : Index K) (ha : ¬ IsMax a) :
    P ((diagram outer.F c).map (homOfLE (Order.le_succ a))) := by
  rcases a with ⟨j, k⟩
  by_cases hk : IsMax k
  · have hj : ¬ IsMax j := fun hj => ha ((flat_isMax_iff j k).2 ⟨hj, hk⟩)
    let targetEq := flat_succ_join (K := K) j k hj hk
    let e := diagramArrowIso outer c
      (show vertex j k ≤ vertex (Order.succ j) (⊥ : K (Order.succ j)) from
        Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj))
      (Order.le_succ (vertex j k)) targetEq.symm
    have h := (P.arrow_mk_iso_iff e).1
    apply h
    change P (indexMap outer.F c (vertex j k) (vertex (Order.succ j) (⊥ : K (Order.succ j)))
      (Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj)))
    exact (congrArg (fun q => P q)
      (indexMap_cross outer.F c (Order.lt_succ_iff_not_isMax.mpr hj) k ⊥)).mpr
      (hjoin j k hj hk)
  · let targetEq := flat_succ_inner (K := K) j k hk
    let e := diagramArrowIso outer c
      (show vertex j k ≤ vertex j (Order.succ k) from Sigma.Lex.right _ _ (Order.le_succ k))
      (Order.le_succ (vertex j k)) targetEq.symm
    apply (P.arrow_mk_iso_iff e).1
    change P (indexMap outer.F c (vertex j k) (vertex j (Order.succ k))
      (Sigma.Lex.right _ _ (Order.le_succ k)))
    exact (congrArg (fun q => P q) (indexMap_inner outer.F c j (Order.le_succ k))).mpr (hc j k hk)

end OriginalCellMaps

section CellularClasses

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (outer.F.map (homOfLE (Order.le_succ j))))

local instance : WellFoundedLT (Index K) := lexWellFounded
/-- The original lexicographic successor order used by cellular normalization. -/
noncomputable local instance normalizationSuccOrder : SuccOrder (Index K) := flatSuccOrder

/-- The original greatest-stage crossing is an isomorphism, derived from its actual inner
colimit. -/
theorem join_isIso (j : J) (k : K j) (hj : ¬ IsMax j) (hk : IsMax k) :
    IsIso (crossMap outer.F c (Order.lt_succ_iff_not_isMax.mpr hj) k (⊥ : K (Order.succ j))) := by
  let _ := inner_endpoint_isIso outer.F c j k hk
  have hmap : outer.F.map (homOfLE (Order.succ_le_of_lt (Order.lt_succ_iff_not_isMax.mpr hj))) =
      𝟙 (outer.F.obj (Order.succ j)) :=
    (congrArg outer.F.map (Subsingleton.elim _ (𝟙 (Order.succ j)))).trans (outer.F.map_id _)
  have hroot : innerRoot outer.F c (Order.succ j) (⊥ : K (Order.succ j)) =
      (c (Order.succ j)).isoBot.inv := by
    dsimp only [innerRoot]
    have he : homOfLE (bot_le : (⊥ : K (Order.succ j)) ≤ ⊥) = 𝟙 (⊥ : K (Order.succ j)) :=
      Subsingleton.elim _ _
    rw [he, Functor.map_id, Category.comp_id]
  have h : crossMap outer.F c (Order.lt_succ_iff_not_isMax.mpr hj) k (⊥ : K (Order.succ j)) =
      (c j).incl.app k ≫ (c (Order.succ j)).isoBot.inv := by
    dsimp only [crossMap]
    rw [hmap]
    exact congrArg (fun t => (c j).incl.app k ≫ t) ((Category.id_comp _).trans hroot)
  rw [h]
  infer_instance

/-- Actual varying inner cellular histories normalize to one presentation of the unchanged original
arrow. -/
noncomputable def normalizeCellular (P : MorphismProperty C)
    (hc : ∀ (j : J) (k : K j) (_ : ¬ IsMax k),
      (MorphismProperty.coproducts.{ν} P).pushouts ((c j).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptySourceColimit : IsColimit emptySource)
    (emptyTargetColimit : IsColimit emptyTarget) :
    (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape (Index K) f where
  toTransfiniteCompositionOfShape := normalizedPresentation outer c
  map_mem a ha := by
    apply normalized_map_mem outer c (MorphismProperty.coproducts.{ν} P).pushouts hc
    · intro j k hj hk
      let _ := join_isIso outer c j k hj hk
      let g : PEmpty.{ν + 1} → C := fun i => i.elim
      let cells := emptyAttachCells (A := g) (B := g)
          (fun i : PEmpty.{ν + 1} => (i.elim : g i ⟶ g i))
        (crossMap outer.F c (Order.lt_succ_iff_not_isMax.mpr hj) k (⊥ : K (Order.succ j)))
        emptySource emptyTarget emptySourceColimit emptyTargetColimit
      exact
        ⟨cells.cofan₁.pt, cells.cofan₂.pt, cells.m, cells.g₁, cells.g₂,
          (MorphismProperty.colimitsOfShape_le_coproducts P PEmpty cells.m
            (MorphismProperty.colimitsOfShape.mk' _ _ _ _ cells.isColimit₁ cells.isColimit₂
              (Discrete.natTrans (fun i : Discrete PEmpty => i.as.elim))
              (fun i : Discrete PEmpty => i.as.elim) _ (fun i => i.as.elim))),
          cells.isPushout⟩
    · exact ha

end CellularClasses

section OriginalLabels

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable {α : J → Type t} {A B : ∀ j, α j → C} (g : ∀ j a, A j a ⟶ B j a)
variable (F : J ⥤ C)
variable (c : ∀ j, RelativeCellComplex.{ν} (fun _ : K j => g j)
  (F.map (homOfLE (Order.le_succ j))))

/-- The actual used cells are indexed by the original outer vertex and original inner cell. -/
abbrev UsedCells := Sigma (fun j : J => (c j).Cells)

/-- An occurring cell retains its actual original generator index. -/
def usedCellType (s : UsedCells g F c) : α s.1 := s.2.i

/-- Its endpoint inclusion is the actual inner cell map followed by the original outer leg. -/
def usedCellEndpoint {Y : C} (ι : F ⟶ (Functor.const J).obj Y) (s : UsedCells g F c) :
    B s.1 (usedCellType g F c s) ⟶ Y :=
  s.2.ι ≫ ι.app (Order.succ s.1)

/-- The occurring cells stay in the maximum of the original outer, inner and attachment
universes. -/
def usedCellsUniverse : Type (max w w' ν) := UsedCells g F c

end OriginalLabels

section WholeRelativeCells

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable {α : J → Type t} {A B : ∀ j, α j → C} (g : ∀ j a, A j a ⟶ B j a)
variable {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
variable (c : ∀ j, RelativeCellComplex.{ν} (fun _ : K j => g j)
  (outer.F.map (homOfLE (Order.le_succ j))))

local instance : WellFoundedLT (Index K) := lexWellFounded
/-- The actual lexicographic successor order for retained relative-cell attachments. -/
noncomputable local instance relativeCellsSuccOrder : SuccOrder (Index K) := flatSuccOrder

/-- The actual original transfinite diagrams underlying each supplied cellular history. -/
abbrev innerPresentations := fun j => (c j).toTransfiniteCompositionOfShape

/-- The original cell-arrow family of the flattened block. -/
def flatCellMap (a : Index K) (b : α (ofLex a).1) : A (ofLex a).1 b ⟶ B (ofLex a).1 b :=
  g (ofLex a).1 b

/-- The actual original inner step and its normalized successor map are isomorphic arrows. -/
noncomputable def innerStepArrowIso (j : J) (k : K j) (hk : ¬ IsMax k) :
    Arrow.mk ((c j).F.map (homOfLE (Order.le_succ k))) ≅
      Arrow.mk ((diagram outer.F (innerPresentations g outer c)).map
        (homOfLE (Order.le_succ (vertex j k)))) :=
  eqToIso (congrArg Arrow.mk
    (indexMap_inner outer.F (innerPresentations g outer c) j (Order.le_succ k)).symm) ≪≫
    diagramArrowIso outer (innerPresentations g outer c)
      (show vertex j k ≤ vertex j (Order.succ k) from Sigma.Lex.right _ _ (Order.le_succ k))
      (Order.le_succ (vertex j k)) (flat_succ_inner (K := K) j k hk).symm

/-- At an inner successor the original attachment is transported only by the exact successor target
equality. -/
noncomputable def innerAttachment (j : J) (k : K j) (hk : ¬ IsMax k) :
    AttachCells.{ν} (g j)
      ((diagram outer.F (innerPresentations g outer c)).map
        (homOfLE (Order.le_succ (vertex j k)))) :=
  ((c j).attachCells k hk).ofArrowIso (innerStepArrowIso g outer c j k hk)

/-- The original cell-label type is unchanged by an inner successor attachment. -/
theorem innerAttachment_labels (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).ι = ((c j).attachCells k hk).ι := by
  unfold innerAttachment
  simp only [AttachCells.ofArrowIso_ι]

/-- The original source cofan point is retained by the normalized inner attachment. -/
theorem innerAttachment_sourcePoint (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).cofan₁.pt = ((c j).attachCells k hk).cofan₁.pt := by
  unfold innerAttachment
  rfl

/-- The original target cofan point is retained by the normalized inner attachment. -/
theorem innerAttachment_targetPoint (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).cofan₂.pt = ((c j).attachCells k hk).cofan₂.pt := by
  unfold innerAttachment
  rfl

/-- The whole original source cofan, including every cell injection, is retained. -/
theorem innerAttachment_sourceCofan (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).cofan₁ ≍ ((c j).attachCells k hk).cofan₁ := by
  unfold innerAttachment
  rfl

/-- The whole original target cofan, including every cell injection, is retained. -/
theorem innerAttachment_targetCofan (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).cofan₂ ≍ ((c j).attachCells k hk).cofan₂ := by
  unfold innerAttachment
  rfl

/-- The original coproduct cell map is retained. -/
theorem innerAttachment_cellMap (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).m ≍ ((c j).attachCells k hk).m := by
  unfold innerAttachment
  rfl

/-- The source attachment map changes only by the standard source component of the displayed Arrow
isomorphisms. -/
theorem innerAttachment_sourceMap (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).g₁ =
      ((c j).attachCells k hk).g₁ ≫ (innerStepArrowIso g outer c j k hk).hom.left := rfl

/-- The target attachment map changes only by the original target equality comparison. -/
theorem innerAttachment_targetMap (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerAttachment g outer c j k hk).g₂ =
      ((c j).attachCells k hk).g₂ ≫ (innerStepArrowIso g outer c j k hk).hom.right := rfl

/-- The whole normalized cellular presentation keeps every original cell attachment and exact empty
join. -/
noncomputable def normalizeRelativeCells
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    RelativeCellComplex.{ν} (flatCellMap (K := K) g) f where
  toTransfiniteCompositionOfShape := normalizedPresentation outer (innerPresentations g outer c)
  attachCells a ha := by
    classical
    rcases a with ⟨j, k⟩
    by_cases hk : IsMax k
    · have hj : ¬ IsMax j := fun hj => ha ((flat_isMax_iff j k).2 ⟨hj, hk⟩)
      let e := diagramArrowIso outer (innerPresentations g outer c)
        (show vertex j k ≤ vertex (Order.succ j) (⊥ : K (Order.succ j)) from
          Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj))
        (Order.le_succ (vertex j k)) (flat_succ_join (K := K) j k hj hk).symm
      let _ := join_isIso outer (innerPresentations g outer c) j k hj hk
      let empty := emptyAttachCells (g j)
        (crossMap outer.F (innerPresentations g outer c)
          (Order.lt_succ_iff_not_isMax.mpr hj) k (⊥ : K (Order.succ j)))
        emptySource emptyTarget hSource hTarget
      let original : AttachCells.{ν} (g j)
          ((diagram outer.F (innerPresentations g outer c)).map
            (homOfLE (show vertex j k ≤ vertex (Order.succ j) (⊥ : K (Order.succ j)) from
              Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj)))) :=
        empty.ofArrowIso (eqToIso (congrArg Arrow.mk
          (indexMap_cross outer.F (innerPresentations g outer c)
            (Order.lt_succ_iff_not_isMax.mpr hj) k ⊥).symm))
      exact original.ofArrowIso e
    · exact innerAttachment g outer c j k hk

end WholeRelativeCells

end CategoryTheory.SmallObject.CellularNormalization
