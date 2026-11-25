/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Original native relative cell complexes as labelled partial-order diagrams

The carrier is the literal native `RelativeCellComplex.Cells` carrier. Cells
at the same native stage are incomparable; a cell precedes every cell at a
strictly later stage. Each vertex is the pushout of its own original cell over
the original native stage object. The original root and every native cell map
are retained. The colimit proof uses the native attachment and continuity
data, and requires no presentability of the root.
-/

@[expose] public section

noncomputable section

universe w t v u

namespace CategoryTheory.SmallObject.NativeRelativeCells

open CategoryTheory.Limits HomotopicalAlgebra LowerSetColimits

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : Type t} {s : α → Arrow C} {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : J) (i : α) => (s i).hom) f)

/-- The order retains all original occurrences, including all simultaneous cells. -/
instance occurrencePartialOrder : PartialOrder c.Cells where
  le a b := a = b ∨ a.j < b.j
  lt a b := a.j < b.j
  le_refl a := Or.inl rfl
  le_trans a b d hab hbd := by
    rcases hab with rfl | hab
    · exact hbd
    rcases hbd with rfl | hbd
    · exact Or.inr hab
    · exact Or.inr (hab.trans hbd)
  le_antisymm a b hab hba := by
    rcases hab with h | hab
    · exact h
    rcases hba with h | hba
    · exact h.symm
    · exact False.elim (lt_asymm hab hba)
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      refine ⟨Or.inr hab, ?_⟩
      rintro (h | hba)
      · exact (lt_irrefl a.j) (h ▸ hab)
      · exact lt_asymm hab hba
    · rintro ⟨h | hab, hba⟩
      · exact False.elim (hba (Or.inl h.symm))
      · exact hab

@[simp]
theorem occurrence_lt_iff (a b : c.Cells) : a < b ↔ a.j < b.j := Iff.rfl

@[simp]
theorem occurrence_le_iff (a b : c.Cells) : a ≤ b ↔ a = b ∨ a.j < b.j := Iff.rfl

/-- The actual stage map is weakly monotone on the original occurrence order. -/
theorem occurrence_stage_monotone : Monotone (fun a : c.Cells => a.j) := by
  intro a b hab
  rcases hab with rfl | hab
  · exact le_rfl
  · exact hab.le

/-- The original stage well order supplies well-foundedness of this partial order. -/
theorem occurrence_wellFounded : WellFounded ((· < ·) : c.Cells → c.Cells → Prop) :=
  InvImage.wf (fun a : c.Cells => a.j) (wellFounded_lt : WellFounded ((· < ·) : J → J → Prop))

/-- The actual cells attached strictly before a native stage. -/
def before (j : J) : LowerSet c.Cells where
  carrier := {a | a.j < j}
  lower' _ _ hab hb := (occurrence_stage_monotone c hab).trans_lt hb

@[simp]
theorem mem_before (j : J) (a : c.Cells) : a ∈ before c j ↔ a.j < j := Iff.rfl

theorem before_mono {j k : J} (h : j ≤ k) : before c j ≤ before c k := by
  exact LowerSet.coe_subset_coe.1 (fun _ ha => ha.trans_le h)

/-- A cell's strict predecessor lower set is exactly the original earlier-stage carrier. -/
theorem predecessor_eq_before (a : c.Cells) : LowerSet.Iio a = before c a.j := rfl

/-- The original root-to-stage map, using the native bottom isomorphism. -/
abbrev rootMap (j : J) : X ⟶ c.F.obj j :=
  c.isoBot.inv ≫ c.F.map (homOfLE bot_le)

@[reassoc]
theorem rootMap_map {j k : J} (h : j ≤ k) :
    rootMap c j ≫ c.F.map (homOfLE h) = rootMap c k := by
  rw [Category.assoc, ← c.F.map_comp]
  rfl

/-- These same root maps form the original natural transformation into the native chain. -/
abbrev rootNatTrans : (Functor.const J).obj X ⟶ c.F where
  app j := rootMap c j
  naturality j k h := by
    change 𝟙 X ≫ rootMap c k = rootMap c j ≫ c.F.map h
    rw [Category.id_comp]
    exact (rootMap_map c (leOfHom h)).symm

/-- The original continuous chain lifted under its arbitrary original source. -/
abbrev stageDiagram : J ⥤ Under X := Under.lift c.F (rootNatTrans c)

/-- The original native stage object under its same arbitrary source. -/
abbrev stageObj (j : J) : Under X := (stageDiagram c).obj j

/-- The original native stage map, with its original under-root equation. -/
abbrev stageMap {j k : J} (h : j ≤ k) : stageObj c j ⟶ stageObj c k :=
  (stageDiagram c).map (homOfLE h)

@[reassoc]
theorem stageMap_comp {j k l : J} (hjk : j ≤ k) (hkl : k ≤ l) :
    stageMap c hjk ≫ stageMap c hkl = stageMap c (hjk.trans hkl) := by
  rw [← (stageDiagram c).map_comp]
  rfl

/-- The original source map of a particular native cell occurrence. -/
abbrev nativeAttaching (a : c.Cells) : (s a.i).left ⟶ c.F.obj a.j :=
  (c.attachCells a.j a.hj).cofan₁.inj a.k ≫ (c.attachCells a.j a.hj).g₁

/-- The original target inclusion of that particular native cell occurrence. -/
abbrev nativeCell (a : c.Cells) : (s a.i).right ⟶ c.F.obj (Order.succ a.j) :=
  (c.attachCells a.j a.hj).cell a.k

/-- The exact individual square follows from the original coproduct pushout. -/
@[reassoc]
theorem native_square (a : c.Cells) :
    nativeAttaching c a ≫ c.F.map (homOfLE (Order.le_succ a.j)) =
      (s a.i).hom ≫ nativeCell c a := by
  dsimp [nativeAttaching, nativeCell, AttachCells.cell, RelativeCellComplex.Cells.i]
  rw [Category.assoc, (c.attachCells a.j a.hj).isPushout.w,
    ← Category.assoc, (c.attachCells a.j a.hj).hm, Category.assoc]

/-- The original root-to-endpoint equation at every native stage. -/
@[reassoc]
theorem rootMap_incl (j : J) : rootMap c j ≫ c.incl.app j = f := by
  change (c.isoBot.inv ≫ c.F.map (homOfLE bot_le)) ≫ c.incl.app j = f
  rw [Category.assoc, (Cocone.mk Y c.incl).w (homOfLE bot_le)]
  exact c.fac

/-- The same original stage-to-endpoint maps promoted under the same root. -/
abbrev stageIncl (j : J) : stageObj c j ⟶ Under.mk f :=
  Under.homMk (c.incl.app j) (rootMap_incl c j)

@[reassoc]
theorem stageMap_incl {j k : J} (h : j ≤ k) :
    stageMap c h ≫ stageIncl c k = stageIncl c j := by
  apply Under.UnderMorphism.ext
  change c.F.map (homOfLE h) ≫ c.incl.app k = c.incl.app j
  exact (Cocone.mk Y c.incl).w (homOfLE h)

/-- The original whole native endpoint cocone under its original arbitrary source. -/
abbrev nativeEndpointCocone : Cocone (stageDiagram c) :=
  Under.liftCocone c.F (rootNatTrans c) (Cocone.mk Y c.incl) f (rootMap_incl c)

/-- Its universal property is derived from the actual native endpoint universal property. -/
abbrev nativeEndpointIsColimit : IsColimit (nativeEndpointCocone c) :=
  Under.isColimitLiftCocone c.F (rootNatTrans c) (Cocone.mk Y c.incl) f
    (rootMap_incl c) c.isColimit

variable [HasPushouts C]

/-- The individual pushout of precisely this original cell over its original native stage. -/
abbrev vertex (a : c.Cells) : Under X :=
  Under.mk (rootMap c a.j ≫ pushout.inl (nativeAttaching c a) (s a.i).hom)

/-- The original native stage inclusion into this individual cell pushout. -/
abbrev stageToVertex (a : c.Cells) : stageObj c a.j ⟶ vertex c a :=
  Under.homMk (pushout.inl (nativeAttaching c a) (s a.i).hom) (by rfl)

/-- The original cell target inclusion into its individual pushout. -/
abbrev vertexCell (a : c.Cells) : (s a.i).right ⟶ (vertex c a).right :=
  pushout.inr (nativeAttaching c a) (s a.i).hom

/-- The individual pushout maps to every later native stage from the original square. -/
abbrev vertexToStageRaw (a : c.Cells) (k : J) (h : Order.succ a.j ≤ k) :
    (vertex c a).right ⟶ c.F.obj k :=
  pushout.desc (c.F.map (homOfLE ((Order.le_succ a.j).trans h)))
    (nativeCell c a ≫ c.F.map (homOfLE h)) (by
      change nativeAttaching c a ≫
        c.F.map (homOfLE (Order.le_succ a.j) ≫ homOfLE h) = _
      rw [c.F.map_comp, ← Category.assoc, native_square c a, Category.assoc])

/-- This actual comparison preserves the same original arbitrary root. -/
abbrev vertexToStage (a : c.Cells) (k : J) (h : Order.succ a.j ≤ k) :
    vertex c a ⟶ stageObj c k :=
  Under.homMk (vertexToStageRaw c a k h) (by
    change (rootMap c a.j ≫ pushout.inl _ _) ≫ vertexToStageRaw c a k h = rootMap c k
    rw [Category.assoc, pushout.inl_desc]
    exact rootMap_map c ((Order.le_succ a.j).trans h))

@[reassoc]
theorem stageToVertex_toStage (a : c.Cells) (k : J) (h : Order.succ a.j ≤ k) :
    stageToVertex c a ≫ vertexToStage c a k h =
      stageMap c ((Order.le_succ a.j).trans h) := by
  apply Under.UnderMorphism.ext
  exact pushout.inl_desc _ _ _

@[reassoc]
theorem vertexCell_toStage (a : c.Cells) (k : J) (h : Order.succ a.j ≤ k) :
    vertexCell c a ≫ (vertexToStage c a k h).right =
      nativeCell c a ≫ c.F.map (homOfLE h) :=
  pushout.inr_desc _ _ _

/-- Every original later-stage comparison is compatible with the actual native chain maps. -/
@[reassoc]
theorem vertexToStage_comp (a : c.Cells) (k l : J)
    (hak : Order.succ a.j ≤ k) (hkl : k ≤ l) :
    vertexToStage c a k hak ≫ stageMap c hkl =
      vertexToStage c a l (hak.trans hkl) := by
  apply Under.UnderMorphism.ext
  change vertexToStageRaw c a k hak ≫ c.F.map (homOfLE hkl) =
    vertexToStageRaw c a l (hak.trans hkl)
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, pushout.inl_desc, ← c.F.map_comp]
    rfl
  · rw [← Category.assoc, pushout.inr_desc, pushout.inr_desc, Category.assoc,
      ← c.F.map_comp]
    rfl

/-- A map in the occurrence partial order preserves the native individual pushouts. -/
def vertexMap {a b : c.Cells} (h : a ≤ b) : vertex c a ⟶ vertex c b := by
  classical
  exact if he : a = b then eqToHom (congrArg (vertex c) he)
    else vertexToStage c a b.j (Order.succ_le_of_lt (h.resolve_left he)) ≫ stageToVertex c b

@[simp]
theorem vertexMap_refl (a : c.Cells) : vertexMap c (le_refl a) = 𝟙 (vertex c a) := by
  classical
  simp only [vertexMap, dite_eq_left rfl, eqToHom_refl]

theorem vertexMap_of_lt {a b : c.Cells} (h : a ≤ b) (hlt : a.j < b.j) :
    vertexMap c h = vertexToStage c a b.j (Order.succ_le_of_lt hlt) ≫ stageToVertex c b := by
  have hne : a ≠ b := by
    intro he
    exact (lt_irrefl a.j) (he ▸ hlt)
  classical
  simp only [vertexMap, dite_eq_right hne]

/-- The complete occurrence-map functions compose with their original stage comparisons. -/
@[reassoc]
theorem vertexMap_comp {a b d : c.Cells} (hab : a ≤ b) (hbd : b ≤ d) :
    vertexMap c hab ≫ vertexMap c hbd = vertexMap c (hab.trans hbd) := by
  by_cases heab : a = b
  · subst b
    simp only [vertexMap_refl, Category.id_comp]
  by_cases hebd : b = d
  · subst d
    simp only [vertexMap_refl, Category.comp_id]
  have hab' : a.j < b.j := hab.resolve_left heab
  have hbd' : b.j < d.j := hbd.resolve_left hebd
  rw [vertexMap_of_lt c hab hab', vertexMap_of_lt c hbd hbd',
    vertexMap_of_lt c (hab.trans hbd) (hab'.trans hbd')]
  rw [Category.assoc, stageToVertex_toStage_assoc, ← Category.assoc, vertexToStage_comp]

/-- The literal occurrence carrier and these original maps form the required diagram. -/
abbrev diagram : c.Cells ⥤ Under X where
  obj a := vertex c a
  map h := vertexMap c (leOfHom h)
  map_id a := vertexMap_refl c a
  map_comp h k := (vertexMap_comp c (leOfHom h) (leOfHom k)).symm

/-- Naturality of the actual vertex-to-stage functions on every earlier occurrence. -/
@[reassoc]
theorem vertexMap_toStage {a b : c.Cells} (hab : a ≤ b) (k : J) (hb : b.j < k) :
    vertexMap c hab ≫ vertexToStage c b k (Order.succ_le_of_lt hb) =
      vertexToStage c a k (Order.succ_le_of_lt
        ((occurrence_stage_monotone c hab).trans_lt hb)) := by
  rcases hab with rfl | hab
  · simp only [vertexMap_refl, Category.id_comp]
  · rw [vertexMap_of_lt c (Or.inr hab) hab,
      Category.assoc, stageToVertex_toStage, vertexToStage_comp]

/-- The original native stage is a cocone on all and only the earlier cell occurrences. -/
abbrev stageCocone (j : J) : Cocone (restriction (diagram c) (before c j)) where
  pt := stageObj c j
  ι :=
    { app a := vertexToStage c a.1 j (Order.succ_le_of_lt a.2)
      naturality a b h := by
        change vertexMap c (leOfHom h) ≫ vertexToStage c b.1 j _ =
          vertexToStage c a.1 j _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact vertexMap_toStage c (leOfHom h) j b.2 }

/-- An actual cocone can be restricted to any included original lower carrier. -/
abbrev restrictCocone {B D : LowerSet c.Cells} (h : B ≤ D)
    (q : Cocone (restriction (diagram c) D)) : Cocone (restriction (diagram c) B) where
  pt := q.pt
  ι :=
    { app a := q.ι.app ⟨a.1, memOfLE h a.2⟩
      naturality a b k := by
        change vertexMap c (leOfHom k) ≫ q.ι.app ⟨b.1, memOfLE h b.2⟩ =
          q.ι.app ⟨a.1, memOfLE h a.2⟩ ≫ 𝟙 _
        rw [Category.comp_id]
        exact q.w
          (homOfLE (leOfHom k) :
            (⟨a.1, memOfLE h a.2⟩ : D) ⟶ (⟨b.1, memOfLE h b.2⟩ : D)) }

/-- A cell vertex maps to the actual original endpoint through its native successor stage. -/
abbrev vertexIncl (a : c.Cells) : vertex c a ⟶ Under.mk f :=
  vertexToStage c a (Order.succ a.j) le_rfl ≫ stageIncl c (Order.succ a.j)

/-- Every permissible later stage gives the same original whole endpoint function. -/
@[reassoc]
theorem vertexToStage_incl (a : c.Cells) (j : J) (h : Order.succ a.j ≤ j) :
    vertexToStage c a j h ≫ stageIncl c j = vertexIncl c a := by
  rw [← vertexToStage_comp c a (Order.succ a.j) j le_rfl h,
    Category.assoc, stageMap_incl]

/-- The individual endpoint cell map is precisely the original native cell inclusion. -/
@[reassoc]
theorem vertexCell_incl (a : c.Cells) :
    vertexCell c a ≫ (vertexIncl c a).right = a.ι := by
  change vertexCell c a ≫ (vertexToStageRaw c a (Order.succ a.j) le_rfl ≫
    c.incl.app (Order.succ a.j)) = nativeCell c a ≫ c.incl.app (Order.succ a.j)
  rw [← Category.assoc, pushout.inr_desc]
  simp only [homOfLE_refl, c.F.map_id, Category.comp_id]

/-- The original occurrence-map functions commute with the original endpoint maps. -/
@[reassoc]
theorem vertexMap_incl {a b : c.Cells} (hab : a ≤ b) :
    vertexMap c hab ≫ vertexIncl c b = vertexIncl c a := by
  have hb : b.j < Order.succ b.j := Order.lt_succ_of_not_isMax b.hj
  rw [vertexIncl, ← Category.assoc, vertexMap_toStage c hab (Order.succ b.j) hb,
    vertexToStage_incl]

/-- The whole original endpoint is a cocone on the literal native cell occurrences. -/
abbrev endpointCocone : Cocone (diagram c) where
  pt := Under.mk f
  ι :=
    { app a := vertexIncl c a
      naturality a b h := by
        change vertexMap c (leOfHom h) ≫ vertexIncl c b = vertexIncl c a ≫ 𝟙 _
        rw [Category.comp_id]
        exact vertexMap_incl c (leOfHom h) }

end CategoryTheory.SmallObject.NativeRelativeCells
