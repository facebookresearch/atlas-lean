/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeRelativeCells

/-!
# Full original native predecessor and endpoint colimits

The colimit of the earlier native cell occurrences is the original native
stage object. Successors use both original coproduct universal properties and
the original native attachment pushout. Limits use the original continuous
chain. The resulting tree has the literal original endpoint arrow.
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
  [HasPushouts C]

/-- The empty earlier-cell stage retains the original bottom isomorphism under X. -/
def stageBotIso : stageObj c ⊥ ≅ Under.mk (𝟙 X) :=
  Under.isoMk c.isoBot (by
    change (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : J) ≤ ⊥))) ≫
      c.isoBot.hom = 𝟙 X
    have hb : (homOfLE (bot_le : (⊥ : J) ≤ ⊥) : (⊥ : J) ⟶ ⊥) = 𝟙 ⊥ :=
      Subsingleton.elim _ _
    rw [hb, c.F.map_id, Category.comp_id, Iso.inv_hom_id])

/-- The full actual earlier-cell cocone at bottom is colimiting, including the empty case. -/
def bottomIsColimit : IsColimit (stageCocone c ⊥) where
  desc q := (stageBotIso c).hom ≫ Under.mkIdInitial.to q.pt
  fac q a := False.elim ((not_lt_bot : ¬ a.1.j < (⊥ : J)) a.2)
  uniq q m _ := by
    apply (cancel_epi (stageBotIso c).inv).1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact Under.mkIdInitial.hom_ext _ _

/-- An original cell's own successor comparison is exactly its original native inclusion. -/
theorem vertexCell_ownStage (a : c.Cells) :
    vertexCell c a ≫ (vertexToStage c a (Order.succ a.j) le_rfl).right = nativeCell c a := by
  simpa only [homOfLE_refl, c.F.map_id, Category.comp_id] using
    vertexCell_toStage c a (Order.succ a.j) le_rfl

section Successor

variable (j : J) (hj : ¬ IsMax j) (hp : IsColimit (stageCocone c j))
  (q : Cocone (restriction (diagram c) (before c (Order.succ j))))

/-- The same actual native occurrence at this successor, without a new cell label. -/
abbrev currentCell (k : (c.attachCells j hj).ι) : c.Cells := ⟨j, hj, k⟩

/-- The literal same current occurrence, with its actual before-successor membership proof. -/
abbrev currentCellAt (k : (c.attachCells j hj).ι) : before c (Order.succ j) :=
  ⟨currentCell c j hj k, (mem_before c _ _).2 (Order.lt_succ_of_not_isMax hj)⟩

/-- The given cell cone restricts to the original previous stage. -/
abbrev successorStageDesc : stageObj c j ⟶ q.pt :=
  hp.desc (restrictCocone c (before_mono c (Order.le_succ j)) q)

/-- Every current cell leg induces the SAME original previous-stage descender. -/
theorem successorCellInput_eq (k : (c.attachCells j hj).ι) :
    stageToVertex c (currentCell c j hj k) ≫
      q.ι.app (currentCellAt c j hj k) =
        successorStageDesc c j hp q := by
  apply hp.hom_ext
  intro a
  have hlt : a.1.j < j := (mem_before c j a.1).1 a.2
  have hab : a.1 ≤ currentCell c j hj k := Or.inr hlt
  change vertexToStage c a.1 j _ ≫
    (stageToVertex c (currentCell c j hj k) ≫ q.ι.app (currentCellAt c j hj k)) = _
  calc
    _ = vertexMap c hab ≫ q.ι.app (currentCellAt c j hj k) := by
      rw [vertexMap_of_lt c hab hlt, Category.assoc]
    _ = q.ι.app ⟨a.1, memOfLE (before_mono c (Order.le_succ j)) a.2⟩ :=
      q.w (homOfLE hab :
        (⟨a.1, memOfLE (before_mono c (Order.le_succ j)) a.2⟩ : before c (Order.succ j)) ⟶
          currentCellAt c j hj k)
    _ = _ := (hp.fac (restrictCocone c (before_mono c (Order.le_succ j)) q) a).symm

/-- The original source of every current cell has its required compatibility equation. -/
theorem successorCellCondition (k : (c.attachCells j hj).ι) :
    nativeAttaching c (currentCell c j hj k) ≫ (successorStageDesc c j hp q).right =
      (s (currentCell c j hj k).i).hom ≫
        (vertexCell c (currentCell c j hj k) ≫
          (q.ι.app (currentCellAt c j hj k)).right) := by
  rw [← successorCellInput_eq c j hj hp q k]
  change nativeAttaching c (currentCell c j hj k) ≫
    (pushout.inl (nativeAttaching c (currentCell c j hj k))
      (s (currentCell c j hj k).i).hom ≫ (q.ι.app (currentCellAt c j hj k)).right) = _
  rw [← Category.assoc, pushout.condition, Category.assoc]

/-- The target coproduct cone consists of EVERY original current cell cone leg. -/
abbrev successorTargetsCofan : Cofan (fun k : (c.attachCells j hj).ι =>
    (s ((c.attachCells j hj).π k)).right) :=
  Cofan.mk q.pt.right (fun k => vertexCell c (currentCell c j hj k) ≫
    (q.ι.app (currentCellAt c j hj k)).right)

/-- The descender uses the original native target coproduct universal property. -/
abbrev successorTargetsDesc : (c.attachCells j hj).cofan₂.pt ⟶ q.pt.right :=
  (c.attachCells j hj).isColimit₂.desc (successorTargetsCofan c j hj q)

@[reassoc]
theorem successorTargetsDesc_fac (k : (c.attachCells j hj).ι) :
    (c.attachCells j hj).cofan₂.inj k ≫ successorTargetsDesc c j hj q =
      vertexCell c (currentCell c j hj k) ≫
        (q.ι.app (currentCellAt c j hj k)).right :=
  (c.attachCells j hj).isColimit₂.fac (successorTargetsCofan c j hj q) ⟨k⟩

/-- The original source coproduct universal property proves the ENTIRE native square. -/
theorem successorRawCondition :
    (c.attachCells j hj).g₁ ≫ (successorStageDesc c j hp q).right =
      (c.attachCells j hj).m ≫ successorTargetsDesc c j hj q := by
  apply (c.attachCells j hj).isColimit₁.hom_ext
  rintro ⟨k⟩
  exact (Category.assoc ((c.attachCells j hj).cofan₁.inj k)
    (c.attachCells j hj).g₁ (successorStageDesc c j hp q).right).symm |>.trans
      (successorCellCondition c j hj hp q k) |>.trans
      (congrArg (fun m => (s (currentCell c j hj k).i).hom ≫ m)
        (successorTargetsDesc_fac c j hj q k).symm) |>.trans
      (Category.assoc (s (currentCell c j hj k).i).hom
        ((c.attachCells j hj).cofan₂.inj k) (successorTargetsDesc c j hj q)).symm |>.trans
      (congrArg (fun m => m ≫ successorTargetsDesc c j hj q)
        ((c.attachCells j hj).hm k).symm) |>.trans (Category.assoc _ _ _)

/-- The whole successor descender is obtained from the ORIGINAL native attachment pushout. -/
abbrev successorDescRaw : c.F.obj (Order.succ j) ⟶ q.pt.right :=
  (c.attachCells j hj).isPushout.desc (successorStageDesc c j hp q).right
    (successorTargetsDesc c j hj q) (successorRawCondition c j hj hp q)

/-- The original native root equation for this actual successor descender. -/
theorem successorDesc_root : rootMap c (Order.succ j) ≫ successorDescRaw c j hj hp q =
    q.pt.hom := by
  calc
    _ = (rootMap c j ≫ c.F.map (homOfLE (Order.le_succ j))) ≫
        successorDescRaw c j hj hp q :=
      congrArg (fun m => m ≫ successorDescRaw c j hj hp q)
        (rootMap_map c (Order.le_succ j)).symm
    _ = rootMap c j ≫ (c.F.map (homOfLE (Order.le_succ j)) ≫
        successorDescRaw c j hj hp q) := Category.assoc _ _ _
    _ = rootMap c j ≫ (successorStageDesc c j hp q).right :=
      congrArg (fun m => rootMap c j ≫ m) ((c.attachCells j hj).isPushout.inl_desc _ _ _)
    _ = _ := Under.w (successorStageDesc c j hp q)

/-- The same full successor descender, retaining the actual arbitrary original root. -/
abbrev successorDesc : stageObj c (Order.succ j) ⟶ q.pt :=
  Under.homMk (successorDescRaw c j hj hp q) (successorDesc_root c j hj hp q)

@[reassoc]
theorem successorDesc_stage : stageMap c (Order.le_succ j) ≫ successorDesc c j hj hp q =
    successorStageDesc c j hp q := by
  apply Under.UnderMorphism.ext
  exact (c.attachCells j hj).isPushout.inl_desc _ _ _

/-- Every original current native cell satisfies its actual target factor equation. -/
@[reassoc]
theorem successorDesc_nativeCell (k : (c.attachCells j hj).ι) :
    nativeCell c (currentCell c j hj k) ≫ (successorDesc c j hj hp q).right =
      vertexCell c (currentCell c j hj k) ≫
        (q.ι.app (currentCellAt c j hj k)).right := by
  exact (Category.assoc ((c.attachCells j hj).cofan₂.inj k)
    (c.attachCells j hj).g₂ (successorDescRaw c j hj hp q)).trans
    (congrArg (fun m => (c.attachCells j hj).cofan₂.inj k ≫ m)
      ((c.attachCells j hj).isPushout.inr_desc _ _ _)) |>.trans
    (successorTargetsDesc_fac c j hj q k)

/-- The same successor descender preserves each individual current-cell cone map. -/
theorem successorDesc_currentCell (k : (c.attachCells j hj).ι) :
    vertexToStage c (currentCell c j hj k) (Order.succ j) le_rfl ≫
      successorDesc c j hj hp q =
        q.ι.app (currentCellAt c j hj k) := by
  have hleft : stageToVertex c (currentCell c j hj k) ≫
      (vertexToStage c (currentCell c j hj k) (Order.succ j) le_rfl ≫
        successorDesc c j hj hp q) =
      stageToVertex c (currentCell c j hj k) ≫ q.ι.app (currentCellAt c j hj k) := by
    calc
      _ = (stageToVertex c (currentCell c j hj k) ≫
          vertexToStage c (currentCell c j hj k) (Order.succ j) le_rfl) ≫
          successorDesc c j hj hp q := (Category.assoc _ _ _).symm
      _ = stageMap c (Order.le_succ j) ≫ successorDesc c j hj hp q :=
        congrArg (fun m => m ≫ successorDesc c j hj hp q)
          (stageToVertex_toStage c (currentCell c j hj k) (Order.succ j) le_rfl)
      _ = successorStageDesc c j hp q := successorDesc_stage c j hj hp q
      _ = _ := (successorCellInput_eq c j hj hp q k).symm
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · exact congrArg Under.Hom.right hleft
  · calc
      _ = (vertexCell c (currentCell c j hj k) ≫
          (vertexToStage c (currentCell c j hj k) (Order.succ j) le_rfl).right) ≫
          (successorDesc c j hj hp q).right := (Category.assoc _ _ _).symm
      _ = nativeCell c (currentCell c j hj k) ≫ (successorDesc c j hj hp q).right :=
        congrArg (fun m => m ≫ (successorDesc c j hj hp q).right)
          (vertexCell_ownStage c (currentCell c j hj k))
      _ = _ := successorDesc_nativeCell c j hj hp q k

/-- The full successor factor law includes every earlier and simultaneous original cell. -/
theorem successorDesc_fac (a : before c (Order.succ j)) :
    (stageCocone c (Order.succ j)).ι.app a ≫ successorDesc c j hj hp q = q.ι.app a := by
  have ha : a.1.j ≤ j := (Order.lt_succ_iff_of_not_isMax hj).1 a.2
  rcases lt_or_eq_of_le ha with ha | ha
  · change vertexToStage c a.1 (Order.succ j) _ ≫ successorDesc c j hj hp q = _
    rw [← vertexToStage_comp c a.1 j (Order.succ j) (Order.succ_le_of_lt ha)
      (Order.le_succ j), Category.assoc, successorDesc_stage]
    exact hp.fac (restrictCocone c (before_mono c (Order.le_succ j)) q) ⟨a.1, ha⟩
  · rcases a with ⟨⟨aj, ahj, ak⟩, ham⟩
    dsimp at ha
    subst aj
    exact successorDesc_currentCell c j hj hp q ak

/-- The ORIGINAL native successor is the colimit of all original earlier cell occurrences. -/
def successorIsColimit : IsColimit (stageCocone c (Order.succ j)) where
  desc q := successorDesc c j hj hp q
  fac q a := successorDesc_fac c j hj hp q a
  uniq q m hm := by
    have hstage : stageMap c (Order.le_succ j) ≫ m = successorStageDesc c j hp q := by
      apply hp.hom_ext
      intro a
      change vertexToStage c a.1 j _ ≫ (stageMap c (Order.le_succ j) ≫ m) = _
      rw [← Category.assoc, vertexToStage_comp]
      rw [hm ⟨a.1, memOfLE (before_mono c (Order.le_succ j)) a.2⟩]
      exact (hp.fac (restrictCocone c (before_mono c (Order.le_succ j)) q) a).symm
    apply Under.UnderMorphism.ext
    apply (c.attachCells j hj).hom_ext
    · exact (congrArg Under.Hom.right hstage).trans
        (congrArg Under.Hom.right (successorDesc_stage c j hj hp q)).symm
    · intro k
      have hk := congrArg (fun p => vertexCell c (currentCell c j hj k) ≫ p.right)
        (hm (currentCellAt c j hj k))
      calc
        _ = (vertexCell c (currentCell c j hj k) ≫
            (vertexToStage c (currentCell c j hj k) (Order.succ j) le_rfl).right) ≫ m.right :=
          congrArg (fun p => p ≫ m.right) (vertexCell_ownStage c (currentCell c j hj k)).symm
        _ = vertexCell c (currentCell c j hj k) ≫
            ((vertexToStage c (currentCell c j hj k) (Order.succ j) le_rfl).right ≫ m.right) :=
          Category.assoc _ _ _
        _ = vertexCell c (currentCell c j hj k) ≫ (q.ι.app (currentCellAt c j hj k)).right := hk
        _ = _ := (successorDesc_nativeCell c j hj hp q k).symm

end Successor

/-- The actual earlier-stage descenders commute with the ORIGINAL native stage maps. -/
theorem stageDesc_naturality {B : LowerSet c.Cells}
    (q : Cocone (restriction (diagram c) B)) {j k : J}
    (hj : before c j ≤ B) (hk : before c k ≤ B) (hjk : j ≤ k)
    (hpj : IsColimit (stageCocone c j)) (hpk : IsColimit (stageCocone c k)) :
    stageMap c hjk ≫ hpk.desc (restrictCocone c hk q) =
      hpj.desc (restrictCocone c hj q) := by
  apply hpj.hom_ext
  intro a
  let a' : before c k := ⟨a.1, memOfLE (before_mono c hjk) a.2⟩
  calc
    _ = (vertexToStage c a.1 j (Order.succ_le_of_lt a.2) ≫ stageMap c hjk) ≫
        hpk.desc (restrictCocone c hk q) := (Category.assoc _ _ _).symm
    _ = vertexToStage c a.1 k (Order.succ_le_of_lt a'.2) ≫
        hpk.desc (restrictCocone c hk q) :=
      congrArg (fun m => m ≫ hpk.desc (restrictCocone c hk q))
        (vertexToStage_comp c a.1 j k (Order.succ_le_of_lt a.2) hjk)
    _ = q.ι.app ⟨a.1, memOfLE hk a'.2⟩ := hpk.fac (restrictCocone c hk q) a'
    _ = _ := (hpj.fac (restrictCocone c hj q) a).symm

section Limit

variable (j : J) (hj : Order.IsSuccLimit j)
  (hp : ∀ k < j, Nonempty (IsColimit (stageCocone c k)))
  (q : Cocone (restriction (diagram c) (before c j)))

/-- The original native strict-stage cocone under the exact root. -/
abbrev nativeLimitCocone : Cocone ((Set.principalSegIio j).monotone.functor ⋙ stageDiagram c) where
  pt := stageObj c j
  ι :=
    { app k := stageMap c (Set.mem_Iio.mp k.2).le
      naturality k l h := by
        change stageMap c (leOfHom h) ≫ stageMap c l.2.le = stageMap c (Set.mem_Iio.mp k.2).le ≫ 𝟙 _
        rw [Category.comp_id, stageMap_comp] }

/-- The full ORIGINAL well-order-continuity UP, lifted under the arbitrary root. -/
def nativeLimitIsColimit : IsColimit (nativeLimitCocone c j) := by
  letI : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  exact Under.isColimitLiftCocone
    ((Set.principalSegIio j).monotone.functor ⋙ c.F)
    (Functor.whiskerLeft (Set.principalSegIio j).monotone.functor (rootNatTrans c))
    ((Set.principalSegIio j).cocone c.F) (rootMap c j)
    (fun k => rootMap_map c k.2.le) (c.F.isColimitOfIsWellOrderContinuous j hj)

/-- The exact previous-stage descenders of the given original lower-cell cone. -/
abbrev limitDescCocone : Cocone ((Set.principalSegIio j).monotone.functor ⋙ stageDiagram c) where
  pt := q.pt
  ι :=
    { app k := (hp k.1 (Set.mem_Iio.mp k.2)).some.desc (restrictCocone c (before_mono c k.2.le) q)
      naturality k l h := by
        exact (stageDesc_naturality c q
          (before_mono c (Set.mem_Iio.mp k.2).le)
          (before_mono c (Set.mem_Iio.mp l.2).le) (leOfHom h)
          (hp k.1 (Set.mem_Iio.mp k.2)).some
          (hp l.1 (Set.mem_Iio.mp l.2)).some).trans (Category.comp_id _).symm }

/-- The original continuous native limit supplies the entire lower-cell descender. -/
abbrev limitDesc : stageObj c j ⟶ q.pt :=
  (nativeLimitIsColimit c j hj).desc (limitDescCocone c j hp q)

/-- Every original earlier cell retains its full limit factor equation. -/
theorem limitDesc_fac (a : before c j) :
    (stageCocone c j).ι.app a ≫ limitDesc c j hj hp q = q.ι.app a := by
  have hk : Order.succ a.1.j < j := hj.succ_lt a.2
  have ha : a.1.j < Order.succ a.1.j := Order.lt_succ_of_not_isMax a.1.hj
  change vertexToStage c a.1 j _ ≫ (nativeLimitIsColimit c j hj).desc _ = _
  rw [← vertexToStage_comp c a.1 (Order.succ a.1.j) j le_rfl hk.le,
    Category.assoc, (nativeLimitIsColimit c j hj).fac
      (limitDescCocone c j hp q) ⟨Order.succ a.1.j, hk⟩]
  exact (hp _ hk).some.fac (restrictCocone c (before_mono c hk.le) q) ⟨a.1, ha⟩

/-- The ORIGINAL native limit stage is the colimit of all earlier native cell occurrences. -/
def limitIsColimit : IsColimit (stageCocone c j) where
  desc q := limitDesc c j hj hp q
  fac q a := limitDesc_fac c j hj hp q a
  uniq q m hm := by
    apply (nativeLimitIsColimit c j hj).hom_ext
    intro k
    apply (hp k.1 (Set.mem_Iio.mp k.2)).some.hom_ext
    intro a
    change vertexToStage c a.1 k.1 _ ≫ (stageMap c (Set.mem_Iio.mp k.2).le ≫ m) = _
    rw [← Category.assoc, vertexToStage_comp,
      hm ⟨a.1, memOfLE (before_mono c k.2.le) a.2⟩,
      (nativeLimitIsColimit c j hj).fac, (hp k.1 (Set.mem_Iio.mp k.2)).some.fac]

end Limit

/-- All original native stages have the full earlier-occurrence universal property. -/
theorem stageIsColimitExists (j : J) : Nonempty (IsColimit (stageCocone c j)) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact ⟨bottomIsColimit c⟩
  | succ j hj hp => exact ⟨successorIsColimit c j hj hp.some⟩
  | isSuccLimit j hj hp => exact ⟨limitIsColimit c j hj hp⟩

/-- Choose the actual UP derived from the original native successor and limit data. -/
def stageIsColimit (j : J) : IsColimit (stageCocone c j) := (stageIsColimitExists c j).some

/-- The whole given original cell cone restricts to any original lower carrier. -/
abbrev restrictWholeCocone (q : Cocone (diagram c)) (B : LowerSet c.Cells) :
    Cocone (restriction (diagram c) B) where
  pt := q.pt
  ι :=
    { app a := q.ι.app a.1
      naturality a b h := by
        change (diagram c).map (homOfLE (leOfHom h)) ≫ q.ι.app b.1 = q.ι.app a.1 ≫ 𝟙 _
        rw [Category.comp_id]
        exact q.w (homOfLE (leOfHom h)) }

/-- The original stage descenders of a whole cell cone form a native-chain cocone. -/
abbrev endpointDescCocone (q : Cocone (diagram c)) : Cocone (stageDiagram c) where
  pt := q.pt
  ι :=
    { app j := (stageIsColimit c j).desc
        (restrictCocone c le_top (restrictWholeCocone c q ⊤))
      naturality j k h := by
        exact (stageDesc_naturality c (restrictWholeCocone c q ⊤) le_top le_top
          (leOfHom h) (stageIsColimit c j) (stageIsColimit c k)).trans
          (Category.comp_id _).symm }

/-- The whole descender uses the ORIGINAL native endpoint cocone. -/
abbrev endpointDesc (q : Cocone (diagram c)) : Under.mk f ⟶ q.pt :=
  (nativeEndpointIsColimit c).desc (endpointDescCocone c q)

/-- Every original native cell has its complete endpoint factor equation. -/
theorem endpointDesc_fac (q : Cocone (diagram c)) (a : c.Cells) :
    vertexIncl c a ≫ endpointDesc c q = q.ι.app a := by
  exact (Category.assoc
    (vertexToStage c a (Order.succ a.j) le_rfl) (stageIncl c (Order.succ a.j))
    ((nativeEndpointIsColimit c).desc (endpointDescCocone c q))).trans
      (congrArg (fun m => vertexToStage c a (Order.succ a.j) le_rfl ≫ m)
        ((nativeEndpointIsColimit c).fac (endpointDescCocone c q) (Order.succ a.j))) |>.trans
      ((stageIsColimit c (Order.succ a.j)).fac
        (restrictCocone c le_top (restrictWholeCocone c q ⊤))
        ⟨a, (mem_before c _ _).2 (Order.lt_succ_of_not_isMax a.hj)⟩)

/-- The literal native occurrence diagram has the full ORIGINAL whole endpoint UP. -/
def endpointIsColimit : IsColimit (endpointCocone c) where
  desc q := endpointDesc c q
  fac q a := endpointDesc_fac c q a
  uniq q m hm := by
    apply (nativeEndpointIsColimit c).hom_ext
    intro j
    apply (stageIsColimit c j).hom_ext
    intro a
    change vertexToStage c a.1 j _ ≫ (stageIncl c j ≫ m) = _
    rw [← Category.assoc, vertexToStage_incl, hm a.1,
      (nativeEndpointIsColimit c).fac, (stageIsColimit c j).fac]

/-- The actual predecessor cocone data constructed from each original native stage. -/
abbrev predecessorColimit (a : c.Cells) :
    ColimitCocone (restriction (diagram c) (LowerSet.Iio a)) where
  cocone := stageCocone c a.j
  isColimit := stageIsColimit c a.j

/-- The derived predecessor map is the original stage-to-individual-pushout map. -/
theorem predecessorMap_eq (a : c.Cells) :
    cellTreePredecessorMap (diagram c) a (predecessorColimit c a) = stageToVertex c a := by
  apply (stageIsColimit c a.j).hom_ext
  intro b
  have hlt : b.1.j < a.j := (mem_before c a.j b.1).1 b.2
  have hb : b.1 < a := (occurrence_lt_iff c b.1 a).2 hlt
  let b' : LowerSet.Iio a := ⟨b.1, hb⟩
  change vertexToStage c b.1 a.j _ ≫
    cellTreePredecessorMap (diagram c) a (predecessorColimit c a) =
      vertexToStage c b.1 a.j _ ≫ stageToVertex c a
  calc
    _ = (diagram c).map (homOfLE hb.le) :=
      cellTreePredecessorMap_fac (diagram c) a (predecessorColimit c a) b'
    _ = _ := vertexMap_of_lt c hb.le hlt

/-- Convert the ACTUAL original native witness to a complete original labelled cell tree. -/
def tree : CellTree s X (P := c.Cells) where
  wellFounded := occurrence_wellFounded c
  diagram := diagram c
  label a := a.i
  predecessor a := predecessorColimit c a
  attaching a := nativeAttaching c a
  cell a := vertexCell c a
  isPushout a := by
    rw [predecessorMap_eq c a]
    exact IsPushout.of_hasPushout (nativeAttaching c a) (s a.i).hom
  endpoint := { cocone := endpointCocone c, isColimit := endpointIsColimit c }

@[simp]
theorem tree_hom : (tree c).hom = f := rfl

@[simp]
theorem tree_label (a : c.Cells) : (tree c).label a = a.i := rfl

/-- The complete original endpoint comparison fixes both source and target literally. -/
def presentation : CellTree.Presentation (s := s) (P := c.Cells) f where
  tree := tree c
  endpointIso := Iso.refl _

/-- Actual ambient working-size colimits construct every original lower-piece UP. -/
abbrev allLowerData [HasColimitsOfSize.{w, w} C] : LowerSetColimitData (diagram c) :=
  (tree c).lowerData

/-- The whole chosen lower-piece functor keeps its actual comparison functions. -/
abbrev allLowerFunctor [HasColimitsOfSize.{w, w} C] : LowerSet c.Cells ⥤ Under X :=
  (allLowerData c).functor

end CategoryTheory.SmallObject.NativeRelativeCells
