/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyClasses
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Monomorphisms and the Reedy left class

For simplicial objects in simplicial sets, the native relative latching
maps are all monomorphisms exactly when the original map is monic.
The proof uses the actual latching colimits and relative pushouts and has
no model-category hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

private theorem common_refinement (T : SSet.{u}) {n a b : ℕ}
    (σ : ⦋n⦌ ⟶ ⦋a⦌) (τ : ⦋n⦌ ⟶ ⦋b⦌) [Epi σ] [Epi τ]
    (x : T _⦋a⦌) (y : T _⦋b⦌) (h : T.map σ.op x = T.map τ.op y) :
    ∃ (d : ℕ) (ρ : ⦋a⦌ ⟶ ⦋d⦌) (κ : ⦋b⦌ ⟶ ⦋d⦌) (t : T _⦋d⦌),
      Epi ρ ∧ Epi κ ∧ σ ≫ ρ = τ ≫ κ ∧
        T.map ρ.op t = x ∧ T.map κ.op t = y := by
  obtain ⟨d, ρ, hρ, t, hx⟩ := T.exists_nonDegenerate x
  obtain ⟨e, κ, hκ, s, hy⟩ := T.exists_nonDegenerate y
  let _ : Epi ρ := hρ
  let _ : Epi κ := hκ
  have hp : T.map σ.op x = T.map (σ ≫ ρ).op t := by
    simpa only [op_comp, Functor.map_comp, comp_apply] using
      congrArg (T.map σ.op) hx
  have hq : T.map σ.op x = T.map (τ ≫ κ).op s := by
    apply h.trans
    simpa only [op_comp, Functor.map_comp, comp_apply] using
      congrArg (T.map τ.op) hy
  have hde : d = e := T.unique_nonDegenerate_dim
    (T.map σ.op x) (σ ≫ ρ) t hp (τ ≫ κ) s hq
  subst e
  have hts : t = s := T.unique_nonDegenerate_simplex
    (T.map σ.op x) (σ ≫ ρ) t hp (τ ≫ κ) s hq
  subst s
  have hcomp : σ ≫ ρ = τ ≫ κ := T.unique_nonDegenerate_map
    (T.map σ.op x) (σ ≫ ρ) t hp (τ ≫ κ) t hq
  exact ⟨d, ρ, κ, t, hρ, hκ, hcomp, hx.symm, hy.symm⟩

private theorem index_common_refinement (T : SSet.{u}) (n : ℕ)
    (a b : latchingIndex n) (x : T.obj a.obj.left) (y : T.obj b.obj.left)
    (h : T.map a.obj.hom x = T.map b.obj.hom y) :
    ∃ (c : latchingIndex n) (ma : c ⟶ a) (mb : c ⟶ b)
      (t : T.obj c.obj.left),
      T.map ma.hom.left t = x ∧ T.map mb.hom.left t = y := by
  let σ : ⦋n⦌ ⟶ ⦋a.obj.left.unop.len⦌ := a.obj.hom.unop
  let τ : ⦋n⦌ ⟶ ⦋b.obj.left.unop.len⦌ := b.obj.hom.unop
  let _ : Epi σ := a.property.1
  let _ : Epi τ := b.property.1
  obtain ⟨d, ρ, κ, t, hρ, hκ, hcomp, hx, hy⟩ :=
    common_refinement T σ τ x y h
  let _ : Epi ρ := hρ
  let _ : Epi κ := hκ
  let c : latchingIndex n :=
    { obj := CostructuredArrow.mk (σ ≫ ρ).op
      property := ⟨by
          change Epi (σ ≫ ρ)
          infer_instance,
        (SimplexCategory.le_of_epi ρ).trans_lt a.property.2⟩ }
  let ma : c ⟶ a := ObjectProperty.homMk
    (CostructuredArrow.homMk ρ.op (by rfl))
  let mb : c ⟶ b := ObjectProperty.homMk
    (CostructuredArrow.homMk κ.op (by
      apply Quiver.Hom.unop_inj
      exact hcomp.symm))
  exact ⟨c, ma, mb, t, hx, hy⟩

private theorem latching_component_injective
    (X : SimplicialObject SSet.{u}) (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((latchingMap X n).app k) := by
  let ev : SSet.{u} ⥤ Type u := SSet.evaluation.obj k
  let F := latchingDiagram X n
  have hc : IsColimit (ev.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves ev (colimit.isColimit F)
  intro x y heq
  obtain ⟨a, xa, ha⟩ := Types.jointly_surjective (F ⋙ ev) hc x
  obtain ⟨b, yb, hb⟩ := Types.jointly_surjective (F ⋙ ev) hc y
  let l := (latchingMap X n).app k
  have hax : l ((latchingι X n a).app k xa) = (X.map a.obj.hom).app k xa :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (latchingMap_ι X n a) k) xa
  have hby : l ((latchingι X n b).app k yb) = (X.map b.obj.hom).app k yb :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (latchingMap_ι X n b) k) yb
  have hxy : (X.map a.obj.hom).app k xa = (X.map b.obj.hom).app k yb :=
    hax.symm.trans ((congrArg l ha).trans
      (heq.trans ((congrArg l hb).symm.trans hby)))
  obtain ⟨c, ma, mb, t, hma, hmb⟩ :=
    index_common_refinement (X ⋙ ev) n a b xa yb hxy
  have hwA : (latchingι X n a).app k ((X.map ma.hom.left).app k t) =
      (latchingι X n c).app k t :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (colimit.w F ma) k) t
  have hwB : (latchingι X n b).app k ((X.map mb.hom.left).app k t) =
      (latchingι X n c).app k t :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (colimit.w F mb) k) t
  exact ha.symm.trans ((congrArg ((latchingι X n a).app k) hma).symm.trans
    (hwA.trans (hwB.symm.trans
      ((congrArg ((latchingι X n b).app k) hmb).trans hb))))

private theorem latching_map_mono (X : SimplicialObject SSet.{u}) (n : ℕ) :
    Mono (latchingMap X n) := by
  let _ : ∀ k : SimplexCategoryᵒᵖ, Mono ((latchingMap X n).app k) :=
    fun k => (mono_iff_injective _).mpr (latching_component_injective X n k)
  exact NatTrans.mono_of_mono_app _

private theorem reflect_degeneracy {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) {a b : SimplexCategoryᵒᵖ} (g : b ⟶ a) [Epi g.unop]
    (hf : Mono (f.app a)) (k : SimplexCategoryᵒᵖ)
    (x : (X.obj a).obj k) (y : (Y.obj b).obj k)
    (heq : (f.app a).app k x = (Y.map g).app k y) :
    ∃ z : (X.obj b).obj k,
      (X.map g).app k z = x ∧ (f.app b).app k z = y := by
  let _ : Mono (f.app a) := hf
  let _ : IsSplitEpi g.unop := isSplitEpi_of_epi g.unop
  let r : a ⟶ b := (section_ g.unop).op
  have hr : g ≫ r = 𝟙 b := by
    apply Quiver.Hom.unop_inj
    exact IsSplitEpi.id g.unop
  let z := (X.map r).app k x
  have hY : Y.map g ≫ Y.map r = 𝟙 (Y.obj b) := by
    rw [← Y.map_comp, hr]
    exact Y.map_id _
  have hz : (f.app b).app k z = y :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality r) k) x).trans
      ((congrArg ((Y.map r).app k) heq).trans
        (ConcreteCategory.congr_hom (NatTrans.congr_app hY k) y))
  refine ⟨z, ?_, hz⟩
  apply CategoryTheory.injective_of_mono ((f.app a).app k)
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality g) k) z).trans
    ((congrArg ((Y.map g).app k) hz).trans heq.symm)

private theorem index_morphism_epi {n : ℕ} {a b : latchingIndex n}
    (m : a ⟶ b) : Epi m.hom.left.unop := by
  have hw : b.obj.hom.unop ≫ m.hom.left.unop = a.obj.hom.unop :=
    congrArg (fun g => g.unop) (CostructuredArrow.w m.hom)
  let _ : Epi (b.obj.hom.unop ≫ m.hom.left.unop) :=
    hw.symm ▸ a.property.1
  exact epi_of_epi b.obj.hom.unop m.hom.left.unop

private theorem latching_square_isPullback {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) [Mono f] (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    IsPullback ((latchingMap X n).app k)
      (((latchingObjectFunctor n).map f).app k)
      ((f.app (op ⦋n⦌)).app k) ((latchingMap Y n).app k) := by
  let _ : Mono (latchingMap X n) := latching_map_mono X n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨(NatTrans.congr_app (latchingMap_naturality n f) k).symm,
    fun x y h => CategoryTheory.injective_of_mono
      ((latchingMap X n).app k) h.1, ?_⟩
  intro x y heq
  let ev : SSet.{u} ⥤ Type u := SSet.evaluation.obj k
  let F := latchingDiagram Y n
  have hc : IsColimit (ev.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves ev (colimit.isColimit F)
  obtain ⟨b, yb, hb⟩ := Types.jointly_surjective (F ⋙ ev) hc y
  have hby : (latchingMap Y n).app k ((latchingι Y n b).app k yb) =
      (Y.map b.obj.hom).app k yb :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (latchingMap_ι Y n b) k) yb
  have hxy : (f.app (op ⦋n⦌)).app k x = (Y.map b.obj.hom).app k yb :=
    heq.trans ((congrArg ((latchingMap Y n).app k) hb).symm.trans hby)
  let _ : Epi b.obj.hom.unop := b.property.1
  obtain ⟨z, hz, hfz⟩ := reflect_degeneracy f b.obj.hom inferInstance k x yb hxy
  refine ⟨(latchingι X n b).app k z, ?_, ?_⟩
  · exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (latchingMap_ι X n b) k) z).trans hz
  · exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (latchingObjectFunctor_map_ι n f b) k) z).trans
      ((congrArg ((latchingι Y n b).app k) hfz).trans hb)

private theorem relative_component_mono {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) [Mono f] (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    Mono ((relativeLatchingMap f n).app k) := by
  let _ : Mono (latchingMap Y n) := latching_map_mono Y n
  let ev : SSet.{u} ⥤ Type u := SSet.evaluation.obj k
  have hpo := (IsPushout.of_hasPushout (latchingMap X n)
    ((latchingObjectFunctor n).map f)).map ev
  exact Types.mono_of_isPushout_of_isPullback hpo (latching_square_isPullback f n k)
    (NatTrans.congr_app (relativeLatchingMap_inl f n) k)
    (NatTrans.congr_app (relativeLatchingMap_inr f n) k)
    (fun x y _ _ h => CategoryTheory.injective_of_mono
      ((latchingMap Y n).app k) h)

private theorem relative_map_mono {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) [Mono f] (n : ℕ) : Mono (relativeLatchingMap f n) := by
  let _ : ∀ k : SimplexCategoryᵒᵖ, Mono ((relativeLatchingMap f n).app k) :=
    fun k => relative_component_mono f n k
  exact NatTrans.mono_of_mono_app _

private theorem latching_functor_component_injective
    {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (hf : ∀ m : ℕ, m < n → Mono (f.app (op ⦋m⦌)))
    (k : SimplexCategoryᵒᵖ) :
    Function.Injective (((latchingObjectFunctor n).map f).app k) := by
  let ev : SSet.{u} ⥤ Type u := SSet.evaluation.obj k
  let F := latchingDiagram X n
  have hc : IsColimit (ev.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves ev (colimit.isColimit F)
  intro x y heq
  obtain ⟨a, xa, ha⟩ := Types.jointly_surjective (F ⋙ ev) hc x
  obtain ⟨b, yb, hb⟩ := Types.jointly_surjective (F ⋙ ev) hc y
  let lf := ((latchingObjectFunctor n).map f).app k
  let ly := (latchingMap Y n).app k
  have hfa : lf ((latchingι X n a).app k xa) =
      (latchingι Y n a).app k ((f.app a.obj.left).app k xa) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (latchingObjectFunctor_map_ι n f a) k) xa
  have hfb : lf ((latchingι X n b).app k yb) =
      (latchingι Y n b).app k ((f.app b.obj.left).app k yb) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (latchingObjectFunctor_map_ι n f b) k) yb
  have hla : ly (lf ((latchingι X n a).app k xa)) =
      (Y.map a.obj.hom).app k ((f.app a.obj.left).app k xa) :=
    (congrArg ly hfa).trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (latchingMap_ι Y n a) k) ((f.app a.obj.left).app k xa))
  have hlb : ly (lf ((latchingι X n b).app k yb)) =
      (Y.map b.obj.hom).app k ((f.app b.obj.left).app k yb) :=
    (congrArg ly hfb).trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (latchingMap_ι Y n b) k) ((f.app b.obj.left).app k yb))
  have himage : (Y.map a.obj.hom).app k ((f.app a.obj.left).app k xa) =
      (Y.map b.obj.hom).app k ((f.app b.obj.left).app k yb) :=
    hla.symm.trans ((congrArg (fun z => ly (lf z)) ha).trans
      ((congrArg ly heq).trans ((congrArg (fun z => ly (lf z)) hb).symm.trans hlb)))
  obtain ⟨d, ma, mb, t, hma, hmb⟩ := index_common_refinement (Y ⋙ ev) n a b
    ((f.app a.obj.left).app k xa) ((f.app b.obj.left).app k yb) himage
  let _ : Epi ma.hom.left.unop := index_morphism_epi ma
  let _ : Epi mb.hom.left.unop := index_morphism_epi mb
  obtain ⟨za, hza, hfza⟩ := reflect_degeneracy f ma.hom.left
    (hf a.obj.left.unop.len a.property.2) k xa t hma.symm
  obtain ⟨zb, hzb, hfzb⟩ := reflect_degeneracy f mb.hom.left
    (hf b.obj.left.unop.len b.property.2) k yb t hmb.symm
  let _ : Mono (f.app d.obj.left) := hf d.obj.left.unop.len d.property.2
  have hz : za = zb := CategoryTheory.injective_of_mono ((f.app d.obj.left).app k)
    (hfza.trans hfzb.symm)
  subst zb
  have hwA : (latchingι X n a).app k ((X.map ma.hom.left).app k za) =
      (latchingι X n d).app k za :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (colimit.w F ma) k) za
  have hwB : (latchingι X n b).app k ((X.map mb.hom.left).app k za) =
      (latchingι X n d).app k za :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (colimit.w F mb) k) za
  exact ha.symm.trans ((congrArg ((latchingι X n a).app k) hza).symm.trans
    (hwA.trans (hwB.symm.trans
      ((congrArg ((latchingι X n b).app k) hzb).trans hb))))

private theorem latching_functor_map_mono_of_lower
    {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (hf : ∀ m : ℕ, m < n → Mono (f.app (op ⦋m⦌))) :
    Mono ((latchingObjectFunctor n).map f) := by
  let _ : ∀ k : SimplexCategoryᵒᵖ,
      Mono (((latchingObjectFunctor n).map f).app k) :=
    fun k => (mono_iff_injective _).mpr (latching_functor_component_injective f n hf k)
  exact NatTrans.mono_of_mono_app _

private theorem relative_inl_mono {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (hf : Mono ((latchingObjectFunctor n).map f)) :
    Mono (pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f)) := by
  let _ : Mono ((latchingObjectFunctor n).map f) := hf
  have component (k : SimplexCategoryᵒᵖ) :
      Mono ((pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f)).app k) := by
    let ev : SSet.{u} ⥤ Type u := SSet.evaluation.obj k
    have hpo := (IsPushout.of_hasPushout (latchingMap X n)
      ((latchingObjectFunctor n).map f)).map ev
    exact Types.pushoutCocone_inr_mono_of_isColimit hpo.flip.isColimit
  let _ : ∀ k : SimplexCategoryᵒᵖ,
      Mono ((pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f)).app k) :=
    component
  exact NatTrans.mono_of_mono_app _

private theorem component_mono_of_relative {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) (hr : ∀ n : ℕ, Mono (relativeLatchingMap f n)) :
    ∀ n : ℕ, Mono (f.app (op ⦋n⦌)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    let _ : Mono ((latchingObjectFunctor n).map f) :=
      latching_functor_map_mono_of_lower f n ih
    let _ : Mono (relativeLatchingMap f n) := hr n
    let _ : Mono (pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f)) :=
      relative_inl_mono f n inferInstance
    have hcomp : Mono (pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f) ≫
        relativeLatchingMap f n) := inferInstance
    exact (relativeLatchingMap_inl f n) ▸ hcomp

/-- The model-free Reedy left class of monomorphisms on simplicial sets
is exactly the monomorphisms of simplicial spaces, in every universe. -/
theorem reedyLeft_monomorphisms_eq :
    reedyLeft (MorphismProperty.monomorphisms SSet.{u}) =
      MorphismProperty.monomorphisms (SimplicialObject SSet.{u}) := by
  ext X Y f
  change (∀ n : ℕ, Mono (relativeLatchingMap f n)) ↔ Mono f
  constructor
  · intro hr
    let _ : ∀ a : SimplexCategoryᵒᵖ, Mono (f.app a) :=
      fun a => component_mono_of_relative f hr a.unop.len
    exact NatTrans.mono_of_mono_app f
  · intro hf
    let _ : Mono f := hf
    intro n
    exact relative_map_mono f n

end CategoryTheory.SimplicialObject
