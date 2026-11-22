/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellWeakLadderBudgets
import MathlibExt.CategoryTheory.Subfunctor.TransfiniteUnion

/-!
# The coherent original regular-rho weak ladder

The actual before-ambient budgets construct original supports and weak
intermediate subarrows at every ordinal. Every predecessor is accumulated
before the next step; the successor target is compared by its actual
equality. Only inclusions of the original intermediate subobjects are
cancelled in the structural naturality proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits Cardinal Opposite
open SimplicialPresheaf.KanWeakInterpolation

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D]

private theorem points_surjective {P Q : SimplicialPresheaf.{u} D}
    (g : P ⟶ Q) [∀ d, Epi (g.app d)] :
    Function.Surjective (fun z : originalTotalPoints P =>
      (⟨z.1, (NatTrans.mapElements (g.app z.1)).obj z.2⟩ : originalTotalPoints Q)) := by
  rintro ⟨d, z⟩
  cases z with
  | @mk n x =>
    have hn : Epi ((g.app d).app n) :=
      (NatTrans.epi_iff_epi_app (g.app d)).mp inferInstance n
    obtain ⟨y, hy⟩ := (epi_iff_surjective ((g.app d).app n)).mp hn x
    refine ⟨⟨d, Functor.elementsMk (P.obj d) n y⟩, ?_⟩
    exact congrArg (fun z => (⟨d, Functor.elementsMk (Q.obj d) n z⟩ :
      originalTotalPoints Q)) hy

private theorem incoming_points {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (a : Arrow (SimplicialPresheaf.{u} D)) (β : a ⟶ Arrow.mk f)
    (μ : Cardinal.{u}) (ha : originalArrowPointBound μ a) :
    originalArrowPointBound μ (Subdiagram.arrow f (Subdiagram.incomingRange f β)) := by
  let : ∀ d, Epi ((Subdiagram.incomingFactor f β).left.app d) := fun d => by
    change Epi (SSet.Subcomplex.toRange (β.left.app d))
    infer_instance
  let : ∀ d, Epi ((Subdiagram.incomingFactor f β).right.app d) := fun d => by
    change Epi (SSet.Subcomplex.toRange (β.right.app d))
    infer_instance
  exact ⟨ha.1.of_surjective _ (points_surjective (Subdiagram.incomingFactor f β).left),
    ha.2.of_surjective _ (points_surjective (Subdiagram.incomingFactor f β).right)⟩

private theorem union_le {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {J : Type u} (s : J → Subdiagram f) (t : Subdiagram f) (h : ∀ j, s j ≤ t) :
    Subdiagram.indexedUnion f s ≤ t := by
  intro d
  exact ⟨iSup_le (fun j => (h j d).1), iSup_le (fun j => (h j d).2)⟩

private theorem cardinal_union_eq {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (μ : Cardinal.{u}) [Fact μ.IsRegular] {J : Type u}
    (s : J → cardinalSubarrowIndex f μ) (hJ : HasCardinalLT J μ) :
    (cardinalSubarrowUnion f μ s hJ).val =
      Subdiagram.indexedUnion f (fun j => (s j).val) := by
  change Subdiagram.indexedUnion f
    (fun j : Shrink.{u} J => (s ((equivShrink.{u} J).symm j)).val) = _
  apply Subdiagram.ext
  funext d
  apply Subtype.ext
  apply Prod.ext
  · exact (equivShrink.{u} J).symm.iSup_comp
      (g := fun j : J => (((s j).val.row d).left (f.app d) : (X.obj d).Subcomplex))
  · exact (equivShrink.{u} J).symm.iSup_comp
      (g := fun j : J => (((s j).val.row d).right (f.app d) : (Y.obj d).Subcomplex))

private def accumulated {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {K : Type u} [LinearOrder K] (initial : Subdiagram f) (α : K)
    (T : Set.Iio α → Subdiagram f) : Subdiagram f :=
  Subdiagram.indexedUnion f (fun z : Option (Set.Iio α) =>
    match z with
    | none => initial
    | some β => T β)

private theorem initial_le_prefix {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {K : Type u} [LinearOrder K] (initial : Subdiagram f) (α : K)
    (T : Set.Iio α → Subdiagram f) : initial ≤ accumulated f initial α T :=
  Subdiagram.le_indexedUnion f (fun z : Option (Set.Iio α) =>
    match z with | none => initial | some β => T β) none

private theorem seed_le_prefix {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {K : Type u} [LinearOrder K] (initial : Subdiagram f) (α : K)
    (T : Set.Iio α → Subdiagram f) (β : Set.Iio α) : T β ≤ accumulated f initial α T :=
  Subdiagram.le_indexedUnion f (fun z : Option (Set.Iio α) =>
    match z with | none => initial | some β => T β) (some β)

variable [Small.{u} D] [LocallySmall.{u} D] {I : Type i} [Small.{u} I]

private structure Stage (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (μ ν : Cardinal.{u}) (hν : Fact ν.IsRegular) where
  A : Subdiagram f
  T : Subdiagram f
  B : Subdiagram ((originalLocalCellReplacement S).map f)
  A_le_T : A ≤ T
  A_points : originalArrowPointBound μ (Subdiagram.arrow f A)
  T_points : originalArrowPointBound ν (Subdiagram.arrow f T)
  B_weak : SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
    (Subdiagram.hom ((originalLocalCellReplacement S).map f) B)
  B_points : originalArrowPointBound ν
    (Subdiagram.arrow ((originalLocalCellReplacement S).map f) B)
  B_ranks : letI : Fact ν.IsRegular := hν
    IsCardinalPresentable (Subdiagram.arrow ((originalLocalCellReplacement S).map f) B).left ν ∧
      IsCardinalPresentable (Subdiagram.arrow ((originalLocalCellReplacement S).map f) B).right ν
  R_points : originalArrowPointBound ν
    ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f A))
  R_ranks : letI : Fact ν.IsRegular := hν
    IsCardinalPresentable ((originalLocalCellReplacement S).mapArrow.obj
      (Subdiagram.arrow f A)).left ν ∧
      IsCardinalPresentable ((originalLocalCellReplacement S).mapArrow.obj
        (Subdiagram.arrow f A)).right ν
  p : (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f A) ⟶
    Subdiagram.arrow ((originalLocalCellReplacement S).map f) B
  q : Subdiagram.arrow ((originalLocalCellReplacement S).map f) B ⟶
    (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f T)
  pq : p ≫ q = (originalLocalCellReplacement S).mapArrow.map (Subdiagram.map f A_le_T)
  p_inc : p ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f) B =
    (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f A)
  q_inc : q ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f T) =
    Subdiagram.inclusion ((originalLocalCellReplacement S).map f) B

section Recursion

variable (S : I → Arrow (SimplicialPresheaf.{u} D))
  {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
  {K : Type u} [LinearOrder K]
  (μ ν : K → Cardinal.{u}) (hμ : ∀ α, Fact (μ α).IsRegular)
  (hν : ∀ α, Fact (ν α).IsRegular)
  (initial : Subdiagram f)
  (hinitial : ∀ α, originalArrowPointBound (μ α) (Subdiagram.arrow f initial))
  (hsmall : ∀ α, HasCardinalLT (Set.Iio α) (μ α))
  (hω : ∀ α, ℵ₀ ≤ μ α)
  (hpred : ∀ β α, β < α → ν β < μ α)
  (step : ∀ α (s : cardinalSubarrowIndex f (μ α)),
    Nonempty {b : Stage S f (μ α) (ν α) (hν α) // b.A = s.val})

include hμ hinitial hsmall hω hpred step in
private theorem exists_chosenStage (α : K)
    (prev : ∀ β : K, β < α → Stage S f (μ β) (ν β) (hν β)) :
    Nonempty {b : Stage S f (μ α) (ν α) (hν α) //
      b.A = accumulated f initial α (fun β => (prev β.val β.property).T)} := by
  let : Fact (μ α).IsRegular := hμ α
  let family : Option (Set.Iio α) → cardinalSubarrowIndex f (μ α) := fun z =>
    match z with
    | none => ⟨initial, hinitial α⟩
    | some β => ⟨(prev β.val β.property).T,
        (prev β.val β.property).T_points.1.of_le (hpred β.val α β.property).le,
        (prev β.val β.property).T_points.2.of_le (hpred β.val α β.property).le⟩
  have hi : HasCardinalLT (Option (Set.Iio α)) (μ α) :=
    (hasCardinalLT_option_iff _ _ (hω α)).mpr (hsmall α)
  let input := cardinalSubarrowUnion f (μ α) family hi
  obtain ⟨b, hb⟩ := (step α input).some
  refine ⟨⟨b, hb.trans ?_⟩⟩
  change (cardinalSubarrowUnion f (μ α) family hi).val = _
  rw [cardinal_union_eq]
  unfold accumulated
  congr 1
  funext z
  cases z <;> rfl

private def chosenStage (α : K)
    (prev : ∀ β : K, β < α → Stage S f (μ β) (ν β) (hν β)) :
    {b : Stage S f (μ α) (ν α) (hν α) //
      b.A = accumulated f initial α (fun β => (prev β.val β.property).T)} :=
  Classical.choice (exists_chosenStage S f μ ν hμ hν initial hinitial hsmall hω hpred step α prev)

variable [WellFoundedLT K]

private def stages : ∀ α : K, Stage S f (μ α) (ν α) (hν α) :=
  WellFounded.fix (inferInstance : WellFoundedLT K)
    (fun α prev => (chosenStage S f μ ν hμ hν initial hinitial hsmall hω hpred step α prev).val)

private theorem stages_eq (α : K) :
    (stages S f μ ν hμ hν initial hinitial hsmall hω hpred step α).A =
      accumulated f initial α (fun β =>
        (stages S f μ ν hμ hν initial hinitial hsmall hω hpred step β.val).T) := by
  rw [stages, WellFounded.fix_eq]
  exact (chosenStage S f μ ν hμ hν initial hinitial hsmall hω hpred step α _).property

end Recursion

private structure Construction (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (K : Type u) [LinearOrder K] (μ ν : K → Cardinal.{u})
    (hν : ∀ α, Fact (ν α).IsRegular) (initial : Subdiagram f) where
  stage : ∀ α, Stage S f (μ α) (ν α) (hν α)
  A_eq : ∀ α, (stage α).A = accumulated f initial α (fun β => (stage β.val).T)

private def construction (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {K : Type u} [LinearOrder K] [WellFoundedLT K]
    (μ ν : K → Cardinal.{u}) (hμ : ∀ α, Fact (μ α).IsRegular)
    (hν : ∀ α, Fact (ν α).IsRegular) (initial : Subdiagram f)
    (hinitial : ∀ α, originalArrowPointBound (μ α) (Subdiagram.arrow f initial))
    (hsmall : ∀ α, HasCardinalLT (Set.Iio α) (μ α))
    (hω : ∀ α, ℵ₀ ≤ μ α) (hpred : ∀ β α, β < α → ν β < μ α)
    (step : ∀ α (s : cardinalSubarrowIndex f (μ α)),
      Nonempty {b : Stage S f (μ α) (ν α) (hν α) // b.A = s.val}) :
    Construction S f K μ ν hν initial where
  stage := stages S f μ ν hμ hν initial hinitial hsmall hω hpred step
  A_eq := stages_eq S f μ ν hμ hν initial hinitial hsmall hω hpred step

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem accumulated_rows {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {K : Type u} [LinearOrder K] (initial : Subdiagram f) (T : K → Subdiagram f)
    (α : K) (d : Dᵒᵖ) :
    ((accumulated f initial α (fun β => T β.val)).row d).left (f.app d) =
      Subfunctor.strictPrefixUnion ((initial.row d).left (f.app d))
        (fun β => ((T β).row d).left (f.app d)) α ∧
    ((accumulated f initial α (fun β => T β.val)).row d).right (f.app d) =
      Subfunctor.strictPrefixUnion ((initial.row d).right (f.app d))
        (fun β => ((T β).row d).right (f.app d)) α := by
  constructor
  · change (⨆ z : Option (Set.Iio α),
      ((match z with | none => initial | some β => T β.val).row d).left (f.app d)) = _
    rw [iSup_option]
    rfl
  · change (⨆ z : Option (Set.Iio α),
      ((match z with | none => initial | some β => T β.val).row d).right (f.app d)) = _
    rw [iSup_option]
    rfl

section Geometry

variable {S : I → Arrow (SimplicialPresheaf.{u} D)}
  {X Y : SimplicialPresheaf.{u} D} {f : X ⟶ Y}
  {K : Type u} [LinearOrder K] {μ ν : K → Cardinal.{u}}
  {hν : ∀ α, Fact (ν α).IsRegular} {initial : Subdiagram f}
  (L : Construction S f K μ ν hν initial)

private theorem A_mono : Monotone (fun α => (L.stage α).A) := by
  intro α β h
  change (L.stage α).A ≤ (L.stage β).A
  rw [L.A_eq α, L.A_eq β]
  intro d
  constructor
  · exact (accumulated_rows f initial (fun γ => (L.stage γ).T) α d).1.le.trans
      ((Subfunctor.strictPrefixUnion_mono _ _ h).trans
        (accumulated_rows f initial (fun γ => (L.stage γ).T) β d).1.symm.le)
  · exact (accumulated_rows f initial (fun γ => (L.stage γ).T) α d).2.le.trans
      ((Subfunctor.strictPrefixUnion_mono _ _ h).trans
        (accumulated_rows f initial (fun γ => (L.stage γ).T) β d).2.symm.le)

private theorem initial_le_A (α : K) : initial ≤ (L.stage α).A := by
  rw [L.A_eq]
  exact initial_le_prefix f initial α _

private theorem earlier_T_le_A {α β : K} (h : α < β) : (L.stage α).T ≤ (L.stage β).A := by
  rw [L.A_eq]
  exact seed_le_prefix f initial β (fun γ => (L.stage γ.val).T) ⟨α, h⟩

private theorem T_mono : Monotone (fun α => (L.stage α).T) := by
  intro α β h
  rcases eq_or_lt_of_le h with e | hlt
  · subst e
    exact le_rfl
  · exact (earlier_T_le_A L hlt).trans (L.stage β).A_le_T

variable [OrderBot K] [SuccOrder K] [NoMaxOrder K]

omit [OrderBot K] in
private theorem T_eq_successor (α : K) : (L.stage α).T = (L.stage (Order.succ α)).A := by
  apply le_antisymm
  · exact earlier_T_le_A L (Order.lt_succ α)
  · rw [L.A_eq]
    apply union_le f _ (L.stage α).T
    intro z
    cases z with
    | none => exact (initial_le_A L α).trans (L.stage α).A_le_T
    | some β => exact T_mono L (Order.lt_succ_iff.mp β.property)

omit [SuccOrder K] [NoMaxOrder K] in
private theorem A_bot : (L.stage (⊥ : K)).A = initial := by
  rw [L.A_eq]
  apply Subdiagram.ext
  funext d
  apply Subtype.ext
  apply Prod.ext
  · exact (accumulated_rows f initial (fun γ => (L.stage γ).T) ⊥ d).1.trans
      (Subfunctor.strictPrefixUnion_bot _ _)
  · exact (accumulated_rows f initial (fun γ => (L.stage γ).T) ⊥ d).2.trans
      (Subfunctor.strictPrefixUnion_bot _ _)

omit [NoMaxOrder K] in
private theorem A_limit (α : K) (hα : Order.IsSuccLimit α) :
    (L.stage α).A = Subdiagram.indexedUnion f (fun β : Set.Iio α => (L.stage β.val).A) := by
  rw [L.A_eq]
  apply Subdiagram.ext
  funext d
  apply Subtype.ext
  apply Prod.ext
  · change ((accumulated f initial α _).row d).left (f.app d) =
      ⨆ β : Set.Iio α, ((L.stage β.val).A.row d).left (f.app d)
    rw [(accumulated_rows f initial (fun γ => (L.stage γ).T) α d).1,
      Subfunctor.strictPrefixUnion_limit _ _ α hα]
    apply iSup_congr
    intro β
    rw [L.A_eq]
    exact (accumulated_rows f initial (fun γ => (L.stage γ).T) β.val d).1.symm
  · change ((accumulated f initial α _).row d).right (f.app d) =
      ⨆ β : Set.Iio α, ((L.stage β.val).A.row d).right (f.app d)
    rw [(accumulated_rows f initial (fun γ => (L.stage γ).T) α d).2,
      Subfunctor.strictPrefixUnion_limit _ _ α hα]
    apply iSup_congr
    intro β
    rw [L.A_eq]
    exact (accumulated_rows f initial (fun γ => (L.stage γ).T) β.val d).2.symm

end Geometry

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem map_refl {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (s : Subdiagram f) (h : s ≤ s) : Subdiagram.map f h = 𝟙 (Subdiagram.arrow f s) := by
  ext d n x <;> rfl

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem map_comp {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {s t v : Subdiagram f} (h : s ≤ t) (k : t ≤ v) :
    Subdiagram.map f h ≫ Subdiagram.map f k = Subdiagram.map f (h.trans k) := by
  ext d n x <;> rfl

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem eq_inclusion {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {s t : Subdiagram f} (h : s = t) :
    eqToHom (congrArg (Subdiagram.arrow f) h) ≫ Subdiagram.inclusion f t =
      Subdiagram.inclusion f s := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem map_eqToHom {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {s t v : Subdiagram f} (h : s ≤ t) (e : t = v) (k : s ≤ v) :
    Subdiagram.map f h ≫ eqToHom (congrArg (Subdiagram.arrow f) e) =
      Subdiagram.map f k := by
  cases e
  simp only [eqToHom_refl, Category.comp_id]

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem le_of_over {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {s t : Subdiagram f} (g : Subdiagram.arrow f s ⟶ Subdiagram.arrow f t)
    (hg : g ≫ Subdiagram.inclusion f t = Subdiagram.inclusion f s) : s ≤ t := by
  intro d
  constructor
  · intro n x hx
    let z : ((s.row d).left (f.app d)).obj n := ⟨x, hx⟩
    have h := congrArg (fun m => ((m.left.app d).app n) z) hg
    change ((g.left.app d).app n z).val = x at h
    exact h ▸ ((g.left.app d).app n z).property
  · intro n x hx
    let z : ((s.row d).right (f.app d)).obj n := ⟨x, hx⟩
    have h := congrArg (fun m => ((m.right.app d).app n) z) hg
    change ((g.right.app d).app n z).val = x at h
    exact h ▸ ((g.right.app d).app n z).property

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem hom_eq_over {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    {s : Subdiagram f} {a : Arrow (SimplicialPresheaf.{u} D)}
    (g h : a ⟶ Subdiagram.arrow f s)
    (e : g ≫ Subdiagram.inclusion f s = h ≫ Subdiagram.inclusion f s) : g = h := by
  apply Arrow.hom_ext
  · apply (cancel_mono (Subdiagram.leftInclusion f s)).mp
    exact congrArg Arrow.Hom.left e
  · apply (cancel_mono (Subdiagram.rightInclusion f s)).mp
    exact congrArg Arrow.Hom.right e

section Structural

variable {S : I → Arrow (SimplicialPresheaf.{u} D)}
  {X Y : SimplicialPresheaf.{u} D} {f : X ⟶ Y}
  {K : Type u} [LinearOrder K] [SuccOrder K] [NoMaxOrder K]
  {μ ν : K → Cardinal.{u}} {hν : ∀ α, Fact (ν α).IsRegular}
  {initial : Subdiagram f} (L : Construction S f K μ ν hν initial)

private def amap {α β : K} (h : α ≤ β) :
    Subdiagram.arrow f (L.stage α).A ⟶ Subdiagram.arrow f (L.stage β).A :=
  Subdiagram.map f (A_mono L h)

private def qmap (α : K) :
    Subdiagram.arrow ((originalLocalCellReplacement S).map f) (L.stage α).B ⟶
      (originalLocalCellReplacement S).mapArrow.obj
          (Subdiagram.arrow f (L.stage (Order.succ α)).A) :=
  (L.stage α).q ≫ (originalLocalCellReplacement S).mapArrow.map
    (eqToHom (congrArg (Subdiagram.arrow f) (T_eq_successor L α)))

private theorem qmap_inclusion (α : K) :
    qmap L α ≫ (originalLocalCellReplacement S).mapArrow.map
      (Subdiagram.inclusion f (L.stage (Order.succ α)).A) =
      Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (L.stage α).B := by
  unfold qmap
  rw [Category.assoc, ← Functor.map_comp, eq_inclusion f (T_eq_successor L α)]
  exact (L.stage α).q_inc

private theorem pq_step (α : K) :
    (L.stage α).p ≫ qmap L α =
      (originalLocalCellReplacement S).mapArrow.map (amap L (Order.le_succ α)) := by
  unfold qmap
  rw [← Category.assoc, (L.stage α).pq, ← Functor.map_comp]
  exact congrArg (originalLocalCellReplacement S).mapArrow.map
    (map_eqToHom f (L.stage α).A_le_T (T_eq_successor L α) (A_mono L (Order.le_succ α)))

private def bComposite {α β : K} (h : α < β) :
    Subdiagram.arrow ((originalLocalCellReplacement S).map f) (L.stage α).B ⟶
      Subdiagram.arrow ((originalLocalCellReplacement S).map f) (L.stage β).B :=
  qmap L α ≫ (originalLocalCellReplacement S).mapArrow.map
    (amap L (Order.succ_le_iff.mpr h)) ≫ (L.stage β).p

private theorem bComposite_over {α β : K} (h : α < β) :
    bComposite L h ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (L.stage β).B =
      Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (L.stage α).B := by
  unfold bComposite
  simp only [Category.assoc]
  rw [(L.stage β).p_inc, ← Functor.map_comp]
  change qmap L α ≫ (originalLocalCellReplacement S).mapArrow.map
    (Subdiagram.map f _ ≫ Subdiagram.inclusion f (L.stage β).A) = _
  rw [Subdiagram.map_inclusion]
  exact qmap_inclusion L α

private theorem B_mono : Monotone (fun α => (L.stage α).B) := by
  intro α β h
  rcases eq_or_lt_of_le h with e | hlt
  · subst e
    exact le_rfl
  · exact le_of_over ((originalLocalCellReplacement S).map f)
      (bComposite L hlt) (bComposite_over L hlt)

private def bmap {α β : K} (h : α ≤ β) :
    Subdiagram.arrow ((originalLocalCellReplacement S).map f) (L.stage α).B ⟶
      Subdiagram.arrow ((originalLocalCellReplacement S).map f) (L.stage β).B :=
  Subdiagram.map ((originalLocalCellReplacement S).map f) (B_mono L h)

private theorem bmap_formula {α β : K} (h : α < β) : bmap L h.le = bComposite L h := by
  apply hom_eq_over ((originalLocalCellReplacement S).map f)
  exact (Subdiagram.map_inclusion _ (B_mono L h.le)).trans (bComposite_over L h).symm

private theorem p_naturality {α β : K} (h : α ≤ β) :
    (originalLocalCellReplacement S).mapArrow.map (amap L h) ≫ (L.stage β).p =
      (L.stage α).p ≫ bmap L h := by
  apply hom_eq_over ((originalLocalCellReplacement S).map f)
  simp only [Category.assoc]
  rw [(L.stage β).p_inc]
  change (originalLocalCellReplacement S).mapArrow.map (amap L h) ≫
    (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f (L.stage β).A) =
      (L.stage α).p ≫ (Subdiagram.map _ _ ≫ Subdiagram.inclusion _ (L.stage β).B)
  rw [Subdiagram.map_inclusion, (L.stage α).p_inc, ← Functor.map_comp]
  exact congrArg (originalLocalCellReplacement S).mapArrow.map
    (Subdiagram.map_inclusion f (A_mono L h))

private theorem q_naturality {α β : K} (h : α ≤ β) :
    bmap L h ≫ qmap L β = qmap L α ≫ (originalLocalCellReplacement S).mapArrow.map
      (amap L (Order.succ_le_succ h)) := by
  rcases eq_or_lt_of_le h with e | hlt
  · subst e
    simp only [bmap, amap, map_refl, Category.id_comp]
    rw [(originalLocalCellReplacement S).mapArrow.map_id, Category.comp_id]
  · rw [bmap_formula L hlt]
    unfold bComposite
    simp only [Category.assoc]
    rw [pq_step L β, ← Functor.map_comp]
    exact congrArg (fun m => qmap L α ≫ (originalLocalCellReplacement S).mapArrow.map m)
      (map_comp f (A_mono L (Order.succ_le_iff.mpr hlt)) (A_mono L (Order.le_succ β)))

private theorem bmap_successor (α : K) :
    bmap L (Order.le_succ α) = qmap L α ≫ (L.stage (Order.succ α)).p := by
  rw [bmap_formula L (Order.lt_succ α)]
  unfold bComposite
  simp only [amap, map_refl]
  rw [(originalLocalCellReplacement S).mapArrow.map_id, Category.id_comp]

end Structural

/-- Before-ambient regular budgets construct the full coherent original
subarrow ladder, its strict mixed maps, genuine limit unions and incoming factors. -/
theorem exists_originalLocalWeakLadder
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ : Cardinal.{u}) [Fact ρ.IsRegular]
    (hκ : (originalLocalCellData S).κ ≤ ρ) (lower : Cardinal.{u}) :
    letI : Nonempty ρ.ord.ToType := by simpa using (show ρ.IsRegular from Fact.out).ne_zero
    letI : OrderBot ρ.ord.ToType := WellFoundedLT.toOrderBot ρ.ord.ToType
    let R := originalLocalCellReplacement S
    ∃ (μ ν : ρ.ord.ToType → Cardinal.{u})
      (hμ : ∀ α, Fact (μ α).IsRegular) (hν : ∀ α, Fact (ν α).IsRegular)
      (γ : Cardinal.{u}) (_hγ : Fact γ.IsRegular),
      lower < γ ∧ ρ < γ ∧ (originalLocalCellData S).κ < γ ∧
      HasCardinalLT ρ.ord.ToType γ ∧ IsCardinalFiltered ρ.ord.ToType ρ ∧
      (∀ α, lower < μ α ∧ ρ < μ α ∧ (originalLocalCellData S).κ < μ α ∧
        μ α < ν α ∧ ν α < γ ∧ originalArrowPointBound (μ α) a ∧
        (letI : Fact (μ α).IsRegular := hμ α
         IsCardinalPresentable a.left (μ α) ∧ IsCardinalPresentable a.right (μ α))) ∧
      (∀ β α, β < α → ν β < μ α) ∧
      ∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y),
        originalLocalEquivalences S f → ∀ β : a ⟶ Arrow.mk f,
        ∃ (A : ρ.ord.ToType → Subdiagram f) (B : ρ.ord.ToType → Subdiagram (R.map f))
          (hA : Monotone A) (hB : Monotone B)
          (p : ∀ α, R.mapArrow.obj (Subdiagram.arrow f (A α)) ⟶ Subdiagram.arrow (R.map f) (B α))
          (q : ∀ α, Subdiagram.arrow (R.map f) (B α) ⟶
            R.mapArrow.obj (Subdiagram.arrow f (A (Order.succ α)))),
          let aMap := fun {α δ : ρ.ord.ToType} (h : α ≤ δ) => Subdiagram.map f (hA h)
          let bMap := fun {α δ : ρ.ord.ToType} (h : α ≤ δ) => Subdiagram.map (R.map f) (hB h)
          let iA := fun α => Subdiagram.inclusion f (A α)
          let iB := fun α => Subdiagram.inclusion (R.map f) (B α)
          A ⊥ = Subdiagram.incomingRange f β ∧
          (∀ α, Order.IsSuccLimit α →
            A α = Subdiagram.indexedUnion f (fun δ : Set.Iio α => A δ.val)) ∧
          (∀ α,
              SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
              (Subdiagram.hom (R.map f) (B α))) ∧
          (∀ α, letI : Fact (ν α).IsRegular := hν α
            originalArrowPointBound (μ α) (Subdiagram.arrow f (A α)) ∧
            originalArrowPointBound (ν α) (Subdiagram.arrow (R.map f) (B α)) ∧
            IsCardinalPresentable (Subdiagram.arrow (R.map f) (B α)).left (ν α) ∧
            IsCardinalPresentable (Subdiagram.arrow (R.map f) (B α)).right (ν α) ∧
            originalArrowPointBound (ν α) (R.mapArrow.obj (Subdiagram.arrow f (A α))) ∧
            IsCardinalPresentable (R.mapArrow.obj (Subdiagram.arrow f (A α))).left (ν α) ∧
            IsCardinalPresentable (R.mapArrow.obj (Subdiagram.arrow f (A α))).right (ν α)) ∧
          originalArrowPointBound γ (Subdiagram.arrow f (Subdiagram.indexedUnion f A)) ∧
          originalArrowPointBound γ (Subdiagram.arrow (R.map f)
              (Subdiagram.indexedUnion (R.map f) B)) ∧
          (∀ α, p α ≫ q α = R.mapArrow.map (aMap (Order.le_succ α)) ∧
            p α ≫ iB α = R.mapArrow.map (iA α) ∧
            q α ≫ R.mapArrow.map (iA (Order.succ α)) = iB α ∧
            (p α).left ≫ (q α).left = (R.mapArrow.map (aMap (Order.le_succ α))).left ∧
            (p α).right ≫ (q α).right = (R.mapArrow.map (aMap (Order.le_succ α))).right ∧
            (p α).left ≫ (iB α).left = (R.mapArrow.map (iA α)).left ∧
            (p α).right ≫ (iB α).right = (R.mapArrow.map (iA α)).right ∧
            (q α).left ≫ (R.mapArrow.map (iA (Order.succ α))).left = (iB α).left ∧
            (q α).right ≫ (R.mapArrow.map (iA (Order.succ α))).right = (iB α).right) ∧
          (∀ α δ (h : α < δ),
            bMap h.le = q α ≫ R.mapArrow.map (aMap (Order.succ_le_of_lt h)) ≫ p δ ∧
            (bMap h.le).left = (q α).left ≫
              (R.mapArrow.map (aMap (Order.succ_le_of_lt h))).left ≫ (p δ).left ∧
            (bMap h.le).right = (q α).right ≫
              (R.mapArrow.map (aMap (Order.succ_le_of_lt h))).right ≫ (p δ).right) ∧
          (∀ α δ (h : α ≤ δ),
            R.mapArrow.map (aMap h) ≫ p δ = p α ≫ bMap h ∧
            bMap h ≫ q δ = q α ≫ R.mapArrow.map (aMap (Order.succ_le_succ h)) ∧
            (R.mapArrow.map (aMap h)).left ≫ (p δ).left = (p α).left ≫ (bMap h).left ∧
            (R.mapArrow.map (aMap h)).right ≫ (p δ).right = (p α).right ≫ (bMap h).right ∧
            (bMap h).left ≫ (q δ).left = (q α).left ≫
              (R.mapArrow.map (aMap (Order.succ_le_succ h))).left ∧
            (bMap h).right ≫ (q δ).right = (q α).right ≫
              (R.mapArrow.map (aMap (Order.succ_le_succ h))).right) ∧
          (∀ α, bMap (Order.le_succ α) = q α ≫ p (Order.succ α) ∧
            (bMap (Order.le_succ α)).left = (q α).left ≫ (p (Order.succ α)).left ∧
            (bMap (Order.le_succ α)).right = (q α).right ≫ (p (Order.succ α)).right) ∧
          (∀ α, aMap (show α ≤ α from le_rfl) = 𝟙 _ ∧
            bMap (show α ≤ α from le_rfl) = 𝟙 _) ∧
          (∀ α δ ε (h : α ≤ δ) (k : δ ≤ ε),
            aMap h ≫ aMap k = aMap (h.trans k) ∧
            bMap h ≫ bMap k = bMap (h.trans k)) ∧
          (∀ α δ (h : α ≤ δ),
            aMap h ≫ iA δ = iA α ∧ bMap h ≫ iB δ = iB α ∧
            (aMap h).left ≫ (iA δ).left = (iA α).left ∧
            (aMap h).right ≫ (iA δ).right = (iA α).right ∧
            (bMap h).left ≫ (iB δ).left = (iB α).left ∧
            (bMap h).right ≫ (iB δ).right = (iB α).right) ∧
          ∃ j : ∀ α, a ⟶ Subdiagram.arrow f (A α),
            (∀ α, j α ≫ iA α = β ∧
              (j α).left ≫ (iA α).left = β.left ∧
              (j α).right ≫ (iA α).right = β.right) ∧
            (∀ α δ (h : α ≤ δ), j α ≫ aMap h = j δ ∧
              (j α).left ≫ (aMap h).left = (j δ).left ∧
              (j α).right ≫ (aMap h).right = (j δ).right) := by
  let : Nonempty ρ.ord.ToType := by simpa using (show ρ.IsRegular from Fact.out).ne_zero
  let : OrderBot ρ.ord.ToType := WellFoundedLT.toOrderBot ρ.ord.ToType
  have hΩρ : ℵ₀ < ρ := (originalLocalCellData S).properties.1.trans_le hκ
  let : NoMaxOrder ρ.ord.ToType := Cardinal.noMaxOrder hΩρ.le
  obtain ⟨μ, ν, hμ, hν, γ, hγ, hLower, hρ, hκγ, hIndex, hFiltered,
    numeric, predecessor, steps, _prefixBudget, finalBudget⟩ :=
      exists_originalLocalWeakLadderBudgets S a ρ hκ lower
  refine ⟨μ, ν, hμ, hν, γ, hγ, hLower, hρ, hκγ, hIndex, hFiltered, numeric, predecessor, ?_⟩
  intro X Y f hf β
  let R := originalLocalCellReplacement S
  let initial := Subdiagram.incomingRange f β
  have hinitial : ∀ α, originalArrowPointBound (μ α) (Subdiagram.arrow f initial) := by
    intro α
    exact incoming_points f a β (μ α) (numeric α).2.2.2.2.2.1
  have hsmall : ∀ α, HasCardinalLT (Set.Iio α) (μ α) := by
    intro α
    have ho : HasCardinalLT ρ.ord.ToType (μ α) := by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using (numeric α).2.1
    exact ho.of_injective Subtype.val Subtype.val_injective
  have hω : ∀ α, ℵ₀ ≤ μ α := fun α => hΩρ.le.trans (numeric α).2.1.le
  have step : ∀ α (s : cardinalSubarrowIndex f (μ α)),
      Nonempty {b : Stage S f (μ α) (ν α) (hν α) // b.A = s.val} := by
    intro α s
    let : Fact (ν α).IsRegular := hν α
    obtain ⟨b, t, hst, p, q, hw, hb, hbl, hbr, hr, hrl, hrr,
      hpq, hp, hq, _hplq, _hprq, _hpl, _hpr, _hql, _hqr⟩ := steps α f hf s
    let st : Stage S f (μ α) (ν α) (hν α) :=
      { A := s.val
        T := t.val
        B := b
        A_le_T := hst
        A_points := s.property
        T_points := t.property
        B_weak := hw
        B_points := hb
        B_ranks := ⟨hbl, hbr⟩
        R_points := hr
        R_ranks := ⟨hrl, hrr⟩
        p := p
        q := q
        pq := hpq
        p_inc := hp
        q_inc := hq }
    exact ⟨⟨st, rfl⟩⟩
  let L := construction S f μ ν hμ hν initial hinitial hsmall hω predecessor step
  let A := fun α => (L.stage α).A
  let B := fun α => (L.stage α).B
  have hA : Monotone A := A_mono L
  have hB : Monotone B := B_mono L
  let p := fun α => (L.stage α).p
  let q := qmap L
  have hAfin : originalArrowPointBound γ (Subdiagram.arrow f (Subdiagram.indexedUnion f A)) := by
    apply finalBudget f A
    intro α
    exact ⟨(L.stage α).A_points.1.of_le (numeric α).2.2.2.1.le,
      (L.stage α).A_points.2.of_le (numeric α).2.2.2.1.le⟩
  have hBfin : originalArrowPointBound γ (Subdiagram.arrow (R.map f)
      (Subdiagram.indexedUnion (R.map f) B)) :=
          finalBudget (R.map f) B (fun α => (L.stage α).B_points)
  refine ⟨A, B, hA, hB, p, q, A_bot L, ?_, ?_, ?_, hAfin, hBfin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A_limit L
  · exact fun α => (L.stage α).B_weak
  · intro α
    exact ⟨(L.stage α).A_points, (L.stage α).B_points,
      (L.stage α).B_ranks.1, (L.stage α).B_ranks.2,
      (L.stage α).R_points, (L.stage α).R_ranks.1, (L.stage α).R_ranks.2⟩
  · intro α
    have h1 := pq_step L α
    have h2 := (L.stage α).p_inc
    have h3 := qmap_inclusion L α
    exact ⟨h1, h2, h3, congrArg Arrow.Hom.left h1, congrArg Arrow.Hom.right h1,
      congrArg Arrow.Hom.left h2, congrArg Arrow.Hom.right h2,
      congrArg Arrow.Hom.left h3, congrArg Arrow.Hom.right h3⟩
  · intro α δ h
    have he := bmap_formula L h
    exact ⟨he, congrArg Arrow.Hom.left he, congrArg Arrow.Hom.right he⟩
  · intro α δ h
    have h1 := p_naturality L h
    have h2 := q_naturality L h
    exact ⟨h1, h2, congrArg Arrow.Hom.left h1, congrArg Arrow.Hom.right h1,
      congrArg Arrow.Hom.left h2, congrArg Arrow.Hom.right h2⟩
  · intro α
    have he := bmap_successor L α
    exact ⟨he, congrArg Arrow.Hom.left he, congrArg Arrow.Hom.right he⟩
  · exact fun α => ⟨map_refl f (A α) _, map_refl (R.map f) (B α) _⟩
  · exact fun α δ ε h k => ⟨map_comp f (hA h) (hA k), map_comp (R.map f) (hB h) (hB k)⟩
  · intro α δ h
    have h1 := Subdiagram.map_inclusion f (hA h)
    have h2 := Subdiagram.map_inclusion (R.map f) (hB h)
    exact ⟨h1, h2, congrArg Arrow.Hom.left h1, congrArg Arrow.Hom.right h1,
      congrArg Arrow.Hom.left h2, congrArg Arrow.Hom.right h2⟩
  · let j := fun α => Subdiagram.incomingFactor f β ≫ Subdiagram.map f (initial_le_A L α)
    refine ⟨j, ?_, ?_⟩
    · intro α
      have he : j α ≫ Subdiagram.inclusion f (A α) = β := by
        dsimp only [j]
        rw [Category.assoc, Subdiagram.map_inclusion]
        exact Subdiagram.incomingFactor_inclusion f β
      exact ⟨he, congrArg Arrow.Hom.left he, congrArg Arrow.Hom.right he⟩
    · intro α δ h
      have he : j α ≫ Subdiagram.map f (hA h) = j δ := by
        dsimp only [j]
        rw [Category.assoc, map_comp]
      exact ⟨he, congrArg Arrow.Hom.left he, congrArg Arrow.Hom.right he⟩

end SimplicialPresheaf.InjectiveKan
