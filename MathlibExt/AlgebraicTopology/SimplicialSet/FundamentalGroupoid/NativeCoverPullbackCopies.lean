/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Copies in a pullback of the native cover

A map into the native cover determines a section of its pullback.  Translating
that same map by the actual deck maps identifies the pullback with the
coproduct of copies of its source.  Freeness and transitivity on every simplex
give the entire coproduct, and multiplication of deck maps gives the left
action on its copy labels.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet.KanComplex

variable {Y K : SSet.{u}} [SSet.KanComplex Y] {y : Y _⦋0⦌}

private abbrev copyGroup (Y : SSet.{u}) (y : Y _⦋0⦌) :=
  End (SSet.FundamentalGroupoid.mk y)

private abbrev copiedPullback (L : K ⟶ nativeCover Y y) : SSet.{u} :=
  pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y)

/-- One copy is the specified map followed by its actual deck translation. -/
def nativeCoverCopyLift (L : K ⟶ nativeCover Y y)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    K ⟶ pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) :=
  pullback.lift (𝟙 K) (L ≫ nativeCoverDeckMap (X := Y) (x := y) a) (by
    let p := nativeCoverProjection Y y
    calc
      (𝟙 K) ≫ (L ≫ p) = L ≫ p := Category.id_comp _
      _ = L ≫ (nativeCoverDeckMap (X := Y) (x := y) a ≫ p) :=
        congrArg (fun f => L ≫ f) (nativeCoverDeckMap_projection (X := Y) (x := y) a).symm
      _ = (L ≫ nativeCoverDeckMap (X := Y) (x := y) a) ≫ p := (Category.assoc _ _ _).symm)

omit [SSet.KanComplex Y] in
/-- A whole translated copy projects to the identity on its original source. -/
theorem nativeCoverCopyLift_fst (L : K ⟶ nativeCover Y y)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    nativeCoverCopyLift L a ≫
        pullback.fst (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      𝟙 K := by
  exact pullback.lift_fst _ _ _

omit [SSet.KanComplex Y] in
/-- Its cover component is the SAME specified source map followed by the actual deck map. -/
theorem nativeCoverCopyLift_snd (L : K ⟶ nativeCover Y y)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    nativeCoverCopyLift L a ≫
        pullback.snd (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      L ≫ nativeCoverDeckMap (X := Y) (x := y) a := by
  exact pullback.lift_snd _ _ _

omit [SSet.KanComplex Y] in
private theorem copiedPullback_obj_ext (L : K ⟶ nativeCover Y y) (n : ℕ)
    {s t : (copiedPullback L) _⦋n⦌}
    (hf : (pullback.fst (L ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌) s =
      (pullback.fst (L ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌) t)
    (hg : (pullback.snd (L ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌) s =
      (pullback.snd (L ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y)).app (Opposite.op ⦋n⦌) t) : s = t := by
  let F := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌)
  have h := (IsPullback.of_hasPullback (L ≫ nativeCoverProjection Y y)
    (nativeCoverProjection Y y)).map F
  exact Types.ext_of_isPullback h hf hg

omit [SSet.KanComplex Y] in
private theorem nativeCoverCopyLift_app_fst (L : K ⟶ nativeCover Y y)
    (n : ℕ) (a : copyGroup Y y) (s : K _⦋n⦌) :
    (pullback.fst (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y)).app
        (Opposite.op ⦋n⦌) ((nativeCoverCopyLift L a).app (Opposite.op ⦋n⦌) s) = s :=
  congrArg (fun f : K ⟶ K => f.app (Opposite.op ⦋n⦌) s)
    (nativeCoverCopyLift_fst L a)

omit [SSet.KanComplex Y] in
private theorem nativeCoverCopyLift_app_snd (L : K ⟶ nativeCover Y y)
    (n : ℕ) (a : copyGroup Y y) (s : K _⦋n⦌) :
    (pullback.snd (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y)).app
        (Opposite.op ⦋n⦌) ((nativeCoverCopyLift L a).app (Opposite.op ⦋n⦌) s) =
      (nativeCoverDeckMap (X := Y) (x := y) a).app (Opposite.op ⦋n⦌)
        (L.app (Opposite.op ⦋n⦌) s) :=
  congrArg (fun f : K ⟶ nativeCover Y y => f.app (Opposite.op ⦋n⦌) s)
    (nativeCoverCopyLift_snd L a)

private theorem nativeCoverCopyLift_app_bijective (L : K ⟶ nativeCover Y y)
    (n : ℕ) :
    Function.Bijective (fun t : Σ _ : copyGroup Y y, K _⦋n⦌ =>
      (nativeCoverCopyLift L t.1).app (Opposite.op ⦋n⦌) t.2) := by
  let P := nativeCover Y y
  let p := nativeCoverProjection Y y
  let W := copiedPullback L
  let q : W ⟶ K := pullback.fst (L ≫ p) p
  let r : W ⟶ P := pullback.snd (L ≫ p) p
  let e := piOneMulEquivFundamentalGroupoidEnd (X := Y) y
  let := nativeCoverPiOneSimplexAction (X := Y) y n
  constructor
  · rintro ⟨a, s⟩ ⟨b, t⟩ h
    have hs : s = t := (nativeCoverCopyLift_app_fst L n a s).symm.trans
      ((congrArg (fun z : W _⦋n⦌ => q.app (Opposite.op ⦋n⦌) z) h).trans
        (nativeCoverCopyLift_app_fst L n b t))
    subst t
    have hd : (nativeCoverDeckMap (X := Y) (x := y) a).app (Opposite.op ⦋n⦌)
          (L.app (Opposite.op ⦋n⦌) s) =
        (nativeCoverDeckMap (X := Y) (x := y) b).app (Opposite.op ⦋n⦌)
          (L.app (Opposite.op ⦋n⦌) s) :=
      (nativeCoverCopyLift_app_snd L n a s).symm.trans
        ((congrArg (fun z : W _⦋n⦌ => r.app (Opposite.op ⦋n⦌) z) h).trans
          (nativeCoverCopyLift_app_snd L n b s))
    have ha : (nativeCoverDeckMap (X := Y) (x := y) (e (e.symm a))).app (Opposite.op ⦋n⦌)
          (L.app (Opposite.op ⦋n⦌) s) =
        (nativeCoverDeckMap (X := Y) (x := y) a).app (Opposite.op ⦋n⦌)
          (L.app (Opposite.op ⦋n⦌) s) :=
      congrArg (fun z : copyGroup Y y => (nativeCoverDeckMap (X := Y) (x := y) z).app
        (Opposite.op ⦋n⦌) (L.app (Opposite.op ⦋n⦌) s)) (e.apply_symm_apply a)
    have hb : (nativeCoverDeckMap (X := Y) (x := y) (e (e.symm b))).app (Opposite.op ⦋n⦌)
          (L.app (Opposite.op ⦋n⦌) s) =
        (nativeCoverDeckMap (X := Y) (x := y) b).app (Opposite.op ⦋n⦌)
          (L.app (Opposite.op ⦋n⦌) s) :=
      congrArg (fun z : copyGroup Y y => (nativeCoverDeckMap (X := Y) (x := y) z).app
        (Opposite.op ⦋n⦌) (L.app (Opposite.op ⦋n⦌) s)) (e.apply_symm_apply b)
    have hab : e.symm a • (L.app (Opposite.op ⦋n⦌) s) =
        e.symm b • (L.app (Opposite.op ⦋n⦌) s) := ha.trans (hd.trans hb.symm)
    have he : e.symm a = e.symm b :=
      (nativeCoverPiOneSimplexAction_free (X := Y) y n (L.app (Opposite.op ⦋n⦌) s)) hab
    have hab' : a = b := e.symm.injective he
    cases hab'
    rfl
  · intro z
    let s := q.app (Opposite.op ⦋n⦌) z
    let t := r.app (Opposite.op ⦋n⦌) z
    have hp : p.app (Opposite.op ⦋n⦌) (L.app (Opposite.op ⦋n⦌) s) =
        p.app (Opposite.op ⦋n⦌) t :=
      congrArg (fun f : W ⟶ Y => f.app (Opposite.op ⦋n⦌) z)
        (pullback.condition (f := L ≫ p) (g := p))
    obtain ⟨a, ha, _⟩ := nativeCoverPiOneSimplexAction_existsUnique_of_projection_eq (X := Y)
      y n (L.app (Opposite.op ⦋n⦌) s) t hp
    refine ⟨⟨e a, s⟩, ?_⟩
    apply copiedPullback_obj_ext L n
    · exact nativeCoverCopyLift_app_fst L n (e a) s
    · exact (nativeCoverCopyLift_app_snd L n (e a) s).trans ha

/-- The actual deck translations form the full coproduct of source copies. -/
def nativeCoverCopyCofan (L : K ⟶ nativeCover Y y) :
    Cofan (fun _ : End (SSet.FundamentalGroupoid.mk y) => K) :=
  Cofan.mk (pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y))
    (nativeCoverCopyLift L)

/-- Freeness and transitivity on every degree prove the entire copy cofan is a colimit. -/
def nativeCoverCopyCofanIsColimit (L : K ⟶ nativeCover Y y) :
    IsColimit (nativeCoverCopyCofan L) := by
  apply evaluationJointlyReflectsColimits
  intro d
  let F := (evaluation SimplexCategoryᵒᵖ (Type u)).obj d
  let c : Cofan (fun _ : copyGroup Y y => K.obj d) :=
    Cofan.mk ((copiedPullback L).obj d) (fun a => (nativeCoverCopyLift L a).app d)
  have hb : Function.Bijective c.cofanTypes.fromSigma :=
    nativeCoverCopyLift_app_bijective L d.unop.len
  have hc : IsColimit c := Classical.choice
    ((Cofan.nonempty_isColimit_iff_bijective_fromSigma c).mpr hb)
  exact (isColimitMapCoconeCofanMkEquiv F (fun _ : copyGroup Y y => K)
    (nativeCoverCopyLift L)).symm hc

/-- The pullback is identified with copies of the actual source, using its
given map to the cover. -/
def nativeCoverPullbackCopiesIso (L : K ⟶ nativeCover Y y) :
    (∐ fun _ : End (SSet.FundamentalGroupoid.mk y) => K) ≅
      pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) := by
  exact IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct (fun _ : copyGroup Y y => K))
    (nativeCoverCopyCofanIsColimit L)

/-- Each copy is exactly the specified original map followed by the actual deck map. -/
theorem nativeCoverPullbackCopiesIso_ι (L : K ⟶ nativeCover Y y)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    CategoryTheory.Limits.Sigma.ι (fun _ : End (SSet.FundamentalGroupoid.mk y) => K) a ≫
        (nativeCoverPullbackCopiesIso L).hom = nativeCoverCopyLift L a := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun _ : copyGroup Y y => K))
    (nativeCoverCopyCofanIsColimit L) ⟨a⟩

/-- Every entire copy projects to the identity on the specified source. -/
theorem nativeCoverPullbackCopiesIso_projection (L : K ⟶ nativeCover Y y) :
    (nativeCoverPullbackCopiesIso L).hom ≫
        pullback.fst (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      CategoryTheory.Limits.Sigma.desc (fun _ : End (SSet.FundamentalGroupoid.mk y) => 𝟙 K) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst (L ≫ nativeCoverProjection Y y)
      (nativeCoverProjection Y y)) (nativeCoverPullbackCopiesIso_ι L a)).trans
        ((nativeCoverCopyLift_fst L a).trans
          (CategoryTheory.Limits.Sigma.ι_comp_desc (fun _ : copyGroup Y y => 𝟙 K) a).symm))

/-- The unit copy is the same specified lift; no replacement cover point is chosen. -/
theorem nativeCoverPullbackCopiesIso_unit (L : K ⟶ nativeCover Y y) :
    CategoryTheory.Limits.Sigma.ι (fun _ : End (SSet.FundamentalGroupoid.mk y) => K) 1 ≫
        (nativeCoverPullbackCopiesIso L).hom =
      pullback.lift (𝟙 K) L (Category.id_comp (L ≫ nativeCoverProjection Y y)) := by
  refine (nativeCoverPullbackCopiesIso_ι L 1).trans ?_
  apply pullback.hom_ext
  · exact (nativeCoverCopyLift_fst L 1).trans (pullback.lift_fst _ _ _).symm
  · exact (nativeCoverCopyLift_snd L 1).trans
      ((congrArg (fun f => L ≫ f) (nativeCoverDeckMap_one (X := Y) (x := y))).trans
        ((Category.comp_id L).trans (pullback.lift_snd _ _ _).symm))

/-- The actual deck map on the same pulled-back cover. -/
def nativeCoverCopyPullbackDeck (L : K ⟶ nativeCover Y y)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) ⟶
      pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ nativeCoverDeckMap (X := Y) (x := y) a) (by
      let p := nativeCoverProjection Y y
      let f : copiedPullback L ⟶ K := pullback.fst (L ≫ p) p
      let r : copiedPullback L ⟶ nativeCover Y y := pullback.snd (L ≫ p) p
      calc
        f ≫ (L ≫ p) = r ≫ p := pullback.condition (f := L ≫ p) (g := p)
        _ = r ≫ (nativeCoverDeckMap (X := Y) (x := y) a ≫ p) :=
          congrArg (fun h => r ≫ h)
            (nativeCoverDeckMap_projection (X := Y) (x := y) a).symm
        _ = (r ≫ nativeCoverDeckMap (X := Y) (x := y) a) ≫ p :=
          (Category.assoc _ _ _).symm)

omit [SSet.KanComplex Y] in
private theorem nativeCoverCopyPullbackDeck_fst (L : K ⟶ nativeCover Y y)
    (a : copyGroup Y y) :
    nativeCoverCopyPullbackDeck L a ≫
        pullback.fst (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      pullback.fst (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) := by
  exact pullback.lift_fst _ _ _

omit [SSet.KanComplex Y] in
private theorem nativeCoverCopyPullbackDeck_snd (L : K ⟶ nativeCover Y y)
    (a : copyGroup Y y) :
    nativeCoverCopyPullbackDeck L a ≫
        pullback.snd (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      pullback.snd (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) ≫
        nativeCoverDeckMap (X := Y) (x := y) a := by
  exact pullback.lift_snd _ _ _

omit [SSet.KanComplex Y] in
/-- Translating a whole copy by a deck map multiplies its label on the left. -/
theorem nativeCoverCopyLift_deck (L : K ⟶ nativeCover Y y)
    (a b : End (SSet.FundamentalGroupoid.mk y)) :
    nativeCoverCopyLift L (a * b) =
      nativeCoverCopyLift L b ≫ nativeCoverCopyPullbackDeck L a := by
  let p := nativeCoverProjection Y y
  let f : copiedPullback L ⟶ K := pullback.fst (L ≫ p) p
  let r : copiedPullback L ⟶ nativeCover Y y := pullback.snd (L ≫ p) p
  apply pullback.hom_ext
  · calc
      nativeCoverCopyLift L (a * b) ≫ f = 𝟙 K := nativeCoverCopyLift_fst L (a * b)
      _ = nativeCoverCopyLift L b ≫ f := (nativeCoverCopyLift_fst L b).symm
      _ = nativeCoverCopyLift L b ≫ (nativeCoverCopyPullbackDeck L a ≫ f) :=
        congrArg (fun h => nativeCoverCopyLift L b ≫ h)
          (nativeCoverCopyPullbackDeck_fst L a).symm
      _ = (nativeCoverCopyLift L b ≫ nativeCoverCopyPullbackDeck L a) ≫ f :=
        (Category.assoc _ _ _).symm
  · calc
      nativeCoverCopyLift L (a * b) ≫ r =
          L ≫ nativeCoverDeckMap (X := Y) (x := y) (a * b) :=
        nativeCoverCopyLift_snd L (a * b)
      _ = L ≫ (nativeCoverDeckMap (X := Y) (x := y) b ≫
          nativeCoverDeckMap (X := Y) (x := y) a) :=
        congrArg (fun h => L ≫ h) (nativeCoverDeckMap_mul (X := Y) (x := y) a b)
      _ = (L ≫ nativeCoverDeckMap (X := Y) (x := y) b) ≫
          nativeCoverDeckMap (X := Y) (x := y) a := (Category.assoc _ _ _).symm
      _ = (nativeCoverCopyLift L b ≫ r) ≫
          nativeCoverDeckMap (X := Y) (x := y) a :=
        congrArg (fun h => h ≫ nativeCoverDeckMap (X := Y) (x := y) a)
          (nativeCoverCopyLift_snd L b).symm
      _ = nativeCoverCopyLift L b ≫
          (r ≫ nativeCoverDeckMap (X := Y) (x := y) a) := Category.assoc _ _ _
      _ = nativeCoverCopyLift L b ≫ (nativeCoverCopyPullbackDeck L a ≫ r) :=
        congrArg (fun h => nativeCoverCopyLift L b ≫ h)
          (nativeCoverCopyPullbackDeck_snd L a).symm
      _ = (nativeCoverCopyLift L b ≫ nativeCoverCopyPullbackDeck L a) ≫ r :=
        (Category.assoc _ _ _).symm

/-- Actual deck translation acts by left multiplication on every copy label. -/
theorem nativeCoverPullbackCopiesIso_deck (L : K ⟶ nativeCover Y y)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    CategoryTheory.Limits.Sigma.map' (fun b : End (SSet.FundamentalGroupoid.mk y) => a * b)
        (fun _ => 𝟙 K) ≫ (nativeCoverPullbackCopiesIso L).hom =
      (nativeCoverPullbackCopiesIso L).hom ≫ nativeCoverCopyPullbackDeck L a := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro b
  calc
    CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) b ≫
        (CategoryTheory.Limits.Sigma.map' (fun c : copyGroup Y y => a * c) (fun _ => 𝟙 K) ≫
          (nativeCoverPullbackCopiesIso L).hom) =
        (CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) b ≫
          CategoryTheory.Limits.Sigma.map' (fun c : copyGroup Y y => a * c) (fun _ => 𝟙 K)) ≫
            (nativeCoverPullbackCopiesIso L).hom := (Category.assoc _ _ _).symm
    _ = (𝟙 K ≫ CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) (a * b)) ≫
        (nativeCoverPullbackCopiesIso L).hom :=
      congrArg (fun h => h ≫ (nativeCoverPullbackCopiesIso L).hom)
        (CategoryTheory.Limits.Sigma.ι_comp_map' (f := fun _ : copyGroup Y y => K)
          (g := fun _ : copyGroup Y y => K) (fun c : copyGroup Y y => a * c)
          (fun _ : copyGroup Y y => (𝟙 K : K ⟶ K)) b)
    _ = nativeCoverCopyLift L (a * b) := by
      rw [Category.id_comp]
      exact nativeCoverPullbackCopiesIso_ι L (a * b)
    _ = nativeCoverCopyLift L b ≫ nativeCoverCopyPullbackDeck L a :=
      nativeCoverCopyLift_deck L a b
    _ = (CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) b ≫
        (nativeCoverPullbackCopiesIso L).hom) ≫ nativeCoverCopyPullbackDeck L a :=
      congrArg (fun h => h ≫ nativeCoverCopyPullbackDeck L a)
        (nativeCoverPullbackCopiesIso_ι L b).symm
    _ = CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) b ≫
        ((nativeCoverPullbackCopiesIso L).hom ≫ nativeCoverCopyPullbackDeck L a) :=
      Category.assoc _ _ _

/-- The map between the literal pullbacks induced by restriction of the specified lift. -/
def nativeCoverCopyBaseChange (L : K ⟶ nativeCover Y y) {A : SSet.{u}} (j : A ⟶ K) :
    pullback ((j ≫ L) ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) ⟶
      pullback (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) :=
  pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _) (by
    let p := nativeCoverProjection Y y
    let f := pullback.fst ((j ≫ L) ≫ p) p
    let r := pullback.snd ((j ≫ L) ≫ p) p
    calc
      (f ≫ j) ≫ (L ≫ p) = f ≫ (j ≫ (L ≫ p)) := Category.assoc _ _ _
      _ = f ≫ ((j ≫ L) ≫ p) :=
        congrArg (fun h => f ≫ h) (Category.assoc j L p).symm
      _ = r ≫ p := pullback.condition (f := (j ≫ L) ≫ p) (g := p))

omit [SSet.KanComplex Y] in
private theorem nativeCoverCopyBaseChange_fst (L : K ⟶ nativeCover Y y)
    {A : SSet.{u}} (j : A ⟶ K) :
    nativeCoverCopyBaseChange L j ≫
        pullback.fst (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      pullback.fst ((j ≫ L) ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) ≫ j := by
  exact pullback.lift_fst _ _ _

omit [SSet.KanComplex Y] in
private theorem nativeCoverCopyBaseChange_snd (L : K ⟶ nativeCover Y y)
    {A : SSet.{u}} (j : A ⟶ K) :
    nativeCoverCopyBaseChange L j ≫
        pullback.snd (L ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) =
      pullback.snd ((j ≫ L) ≫ nativeCoverProjection Y y) (nativeCoverProjection Y y) := by
  exact pullback.lift_snd _ _ _

omit [SSet.KanComplex Y] in
/-- Restricting each whole translated copy retains the same cover lift. -/
theorem nativeCoverCopyLift_baseChange (L : K ⟶ nativeCover Y y)
    {A : SSet.{u}} (j : A ⟶ K) (a : End (SSet.FundamentalGroupoid.mk y)) :
    j ≫ nativeCoverCopyLift L a =
      nativeCoverCopyLift (j ≫ L) a ≫ nativeCoverCopyBaseChange L j := by
  let p := nativeCoverProjection Y y
  let f : copiedPullback L ⟶ K := pullback.fst (L ≫ p) p
  let r : copiedPullback L ⟶ nativeCover Y y := pullback.snd (L ≫ p) p
  let fa := pullback.fst ((j ≫ L) ≫ p) p
  let ra := pullback.snd ((j ≫ L) ≫ p) p
  apply pullback.hom_ext
  · calc
      (j ≫ nativeCoverCopyLift L a) ≫ f =
          j ≫ (nativeCoverCopyLift L a ≫ f) := Category.assoc _ _ _
      _ = j ≫ 𝟙 K := congrArg (fun h => j ≫ h) (nativeCoverCopyLift_fst L a)
      _ = j := Category.comp_id j
      _ = (𝟙 A) ≫ j := (Category.id_comp j).symm
      _ = (nativeCoverCopyLift (j ≫ L) a ≫ fa) ≫ j :=
        congrArg (fun h => h ≫ j) (nativeCoverCopyLift_fst (j ≫ L) a).symm
      _ = nativeCoverCopyLift (j ≫ L) a ≫ (fa ≫ j) := Category.assoc _ _ _
      _ = nativeCoverCopyLift (j ≫ L) a ≫ (nativeCoverCopyBaseChange L j ≫ f) :=
        congrArg (fun h => nativeCoverCopyLift (j ≫ L) a ≫ h)
          (nativeCoverCopyBaseChange_fst L j).symm
      _ = (nativeCoverCopyLift (j ≫ L) a ≫ nativeCoverCopyBaseChange L j) ≫ f :=
        (Category.assoc _ _ _).symm
  · calc
      (j ≫ nativeCoverCopyLift L a) ≫ r =
          j ≫ (nativeCoverCopyLift L a ≫ r) := Category.assoc _ _ _
      _ = j ≫ (L ≫ nativeCoverDeckMap (X := Y) (x := y) a) :=
        congrArg (fun h => j ≫ h) (nativeCoverCopyLift_snd L a)
      _ = (j ≫ L) ≫ nativeCoverDeckMap (X := Y) (x := y) a :=
        (Category.assoc _ _ _).symm
      _ = nativeCoverCopyLift (j ≫ L) a ≫ ra :=
        (nativeCoverCopyLift_snd (j ≫ L) a).symm
      _ = nativeCoverCopyLift (j ≫ L) a ≫ (nativeCoverCopyBaseChange L j ≫ r) :=
        congrArg (fun h => nativeCoverCopyLift (j ≫ L) a ≫ h)
          (nativeCoverCopyBaseChange_snd L j).symm
      _ = (nativeCoverCopyLift (j ≫ L) a ≫ nativeCoverCopyBaseChange L j) ≫ r :=
        (Category.assoc _ _ _).symm

/-- The full copy identification retains every restriction of the same source map. -/
theorem nativeCoverPullbackCopiesIso_baseChange (L : K ⟶ nativeCover Y y)
    {A : SSet.{u}} (j : A ⟶ K) :
    CategoryTheory.Limits.Sigma.map (fun _ : End (SSet.FundamentalGroupoid.mk y) => j) ≫
        (nativeCoverPullbackCopiesIso L).hom =
      (nativeCoverPullbackCopiesIso (j ≫ L)).hom ≫ nativeCoverCopyBaseChange L j := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro a
  calc
    CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => A) a ≫
        (CategoryTheory.Limits.Sigma.map (fun _ : copyGroup Y y => j) ≫
          (nativeCoverPullbackCopiesIso L).hom) =
        (CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => A) a ≫
          CategoryTheory.Limits.Sigma.map (fun _ : copyGroup Y y => j)) ≫
            (nativeCoverPullbackCopiesIso L).hom := (Category.assoc _ _ _).symm
    _ = (j ≫ CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) a) ≫
        (nativeCoverPullbackCopiesIso L).hom :=
      congrArg (fun h => h ≫ (nativeCoverPullbackCopiesIso L).hom)
        (CategoryTheory.Limits.Sigma.ι_map (fun _ : copyGroup Y y => j) a)
    _ = j ≫ (CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => K) a ≫
        (nativeCoverPullbackCopiesIso L).hom) := Category.assoc _ _ _
    _ = j ≫ nativeCoverCopyLift L a :=
      congrArg (fun h => j ≫ h) (nativeCoverPullbackCopiesIso_ι L a)
    _ = nativeCoverCopyLift (j ≫ L) a ≫ nativeCoverCopyBaseChange L j :=
      nativeCoverCopyLift_baseChange L j a
    _ = (CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => A) a ≫
        (nativeCoverPullbackCopiesIso (j ≫ L)).hom) ≫ nativeCoverCopyBaseChange L j :=
      congrArg (fun h => h ≫ nativeCoverCopyBaseChange L j)
        (nativeCoverPullbackCopiesIso_ι (j ≫ L) a).symm
    _ = CategoryTheory.Limits.Sigma.ι (fun _ : copyGroup Y y => A) a ≫
        ((nativeCoverPullbackCopiesIso (j ≫ L)).hom ≫ nativeCoverCopyBaseChange L j) :=
      Category.assoc _ _ _

end SSet.KanComplex

end
