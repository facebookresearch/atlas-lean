/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Ext¹ from a projective presentation

For a short exact complex `S`, the connecting map sends
`k : S.X₁ ⟶ Y` to `S.extClass.comp (Ext.mk₀ k)`. Its kernel consists of
maps extending across `S.f`. When `S.X₂` is projective, it is surjective
and identifies Ext¹ with the cokernel of precomposition by `S.f`.

The comparison is contravariantly natural in `S` and covariantly natural
in `Y`. `HasExt` may use an independent universe; the ordinary Hom model
uses the corresponding `ULift` to the maximum carrier universe.
-/

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory

open Abelian Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace Abelian

section LiftedHom

variable [Preadditive C]

/-- The ordinary Hom group in the common object and morphism universe. -/
def liftedHom (X Y : C) : AddCommGrpCat.{max u v} :=
  AddCommGrpCat.uliftFunctor.{u, v}.obj (AddCommGrpCat.of (X ⟶ Y))

/-- Precomposition and postcomposition on the universe-lifted Hom group. -/
def liftedHomMap {X X' Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') :
    liftedHom X Y ⟶ liftedHom X' Y' :=
  AddCommGrpCat.uliftFunctor.{u, v}.map
    (((preadditiveYoneda.obj Y).map a.op) ≫
      (preadditiveYoneda.map b).app (op X'))

/-- The lifted map retains the order of the two compositions. -/
lemma liftedHomMap_apply {X X' Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y')
    (k : ULift.{u, v} (X ⟶ Y)) :
    liftedHomMap a b k = ULift.up ((a ≫ k.down) ≫ b) := rfl

end LiftedHom

end Abelian

namespace ShortComplex.ShortExact

variable [Abelian C]

section NativeExt

variable [HasExt.{w} C] {S S' : ShortComplex C}

/-- The degree-zero presentation followed by its positive Yoneda connecting map. -/
def extPresentationSequence (hS : S.ShortExact) (Y : C) :
    ShortComplex AddCommGrpCat.{w} :=
  ShortComplex.mk
    (AddCommGrpCat.ofHom ((Ext.mk₀ S.f).precomp Y (zero_add 0)))
    (AddCommGrpCat.ofHom (hS.extClass.precomp Y (add_zero 1))) (by
      apply AddCommGrpCat.ext
      intro e
      change hS.extClass.comp ((Ext.mk₀ S.f).comp e (zero_add 0)) (add_zero 1) = 0
      exact hS.extClass_comp_assoc e)

/-- The presentation is exact before any projectivity assumption. -/
lemma extPresentationSequence_exact (hS : S.ShortExact) (Y : C) :
    (hS.extPresentationSequence Y).Exact :=
  Ext.contravariant_sequence_exact₁' hS Y 0 1 (add_zero 1)

/-- Projectivity of the middle object makes the Yoneda connecting map surjective. -/
lemma extPresentationSequence_epi (hS : S.ShortExact) (Y : C) [Projective S.X₂] :
    Epi (hS.extPresentationSequence Y).g := by
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro e
  obtain ⟨k, hk⟩ := Ext.contravariant_sequence_exact₃ hS Y e
    (Ext.eq_zero_of_projective ((Ext.mk₀ S.g).comp e (zero_add 1)))
    (n₀ := 0) (add_zero 1)
  exact ⟨k, hk⟩

/-- The cokernel of the degree-zero presentation is the Ext¹ group. -/
def extPresentationCokernelIso (hS : S.ShortExact) (Y : C) [Projective S.X₂] :
    cokernel (hS.extPresentationSequence Y).f ≅
      (hS.extPresentationSequence Y).X₃ := by
  letI := hS.extPresentationSequence_epi Y
  exact (cokernelIsCokernel (hS.extPresentationSequence Y).f).coconePointUniqueUpToIso
    (hS.extPresentationSequence_exact Y).gIsCokernel

/-- The cokernel comparison factors the connecting arrow. -/
@[reassoc]
lemma extPresentationCokernelIso_π_hom (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] :
    cokernel.π (hS.extPresentationSequence Y).f ≫
      (hS.extPresentationCokernelIso Y).hom = (hS.extPresentationSequence Y).g := by
  letI := hS.extPresentationSequence_epi Y
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (hS.extPresentationSequence Y).f)
    (hS.extPresentationSequence_exact Y).gIsCokernel WalkingParallelPair.one

/-- The forward comparison is the universal descent of the connecting map. -/
lemma extPresentationCokernelIso_hom (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] :
    (hS.extPresentationCokernelIso Y).hom =
      cokernel.desc (hS.extPresentationSequence Y).f
        (hS.extPresentationSequence Y).g (hS.extPresentationSequence Y).zero := by
  apply (cancel_epi (cokernel.π (hS.extPresentationSequence Y).f)).1
  rw [extPresentationCokernelIso_π_hom, cokernel.π_desc]

/-- Every degree-zero representative is sent to its Yoneda product. -/
lemma extPresentationCokernelIso_apply (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] (e : Ext S.X₁ Y 0) :
    (hS.extPresentationCokernelIso Y).hom
      (cokernel.π (hS.extPresentationSequence Y).f e) =
        hS.extClass.comp e (add_zero 1) :=
  ConcreteCategory.congr_hom (hS.extPresentationCokernelIso_π_hom Y) e

/-- Vanishing of the extension product is exactly extension across S.f. -/
lemma extClass_comp_mk₀_eq_zero_iff (hS : S.ShortExact) {Y : C} (k : S.X₁ ⟶ Y) :
    hS.extClass.comp (Ext.mk₀ k) (add_zero 1) = 0 ↔
      ∃ l : S.X₂ ⟶ Y, S.f ≫ l = k := by
  constructor
  · intro hk
    obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ k)
      (add_zero 1) hk
    refine ⟨Ext.addEquiv₀ e, ?_⟩
    apply (Ext.mk₀_bijective S.X₁ Y).1
    simpa only [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply] using he
  · rintro ⟨l, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ l)

/-- A map of short exact complexes acts contravariantly, and a target map covariantly. -/
def extPresentationMap (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') :
    hS.extPresentationSequence Y ⟶ hS'.extPresentationSequence Y' where
  τ₁ := ((extFunctor 0).map φ.τ₂.op).app Y ≫ (extFunctorObj S'.X₂ 0).map b
  τ₂ := ((extFunctor 0).map φ.τ₁.op).app Y ≫ (extFunctorObj S'.X₁ 0).map b
  τ₃ := ((extFunctor 1).map φ.τ₃.op).app Y ≫ (extFunctorObj S'.X₃ 1).map b
  comm₁₂ := by
    apply AddCommGrpCat.ext
    intro e
    change (Ext.mk₀ S'.f).comp
        (((Ext.mk₀ φ.τ₂).comp e (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0))
        (zero_add 0) =
      ((Ext.mk₀ φ.τ₁).comp ((Ext.mk₀ S.f).comp e (zero_add 0))
        (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0)
    have h : (Ext.mk₀ S'.f).comp (Ext.mk₀ φ.τ₂) (zero_add 0) =
        (Ext.mk₀ φ.τ₁).comp (Ext.mk₀ S.f) (zero_add 0) := by
      simpa only [Ext.mk₀_comp_mk₀] using
        congrArg (fun k : S'.X₁ ⟶ S.X₂ => Ext.mk₀ k) φ.comm₁₂.symm
    calc
      _ = ((Ext.mk₀ S'.f).comp
          ((Ext.mk₀ φ.τ₂).comp e (zero_add 0)) (zero_add 0)).comp
          (Ext.mk₀ b) (add_zero 0) :=
        (Ext.comp_assoc (Ext.mk₀ S'.f)
          ((Ext.mk₀ φ.τ₂).comp e (zero_add 0)) (Ext.mk₀ b) rfl rfl rfl).symm
      _ = (((Ext.mk₀ S'.f).comp (Ext.mk₀ φ.τ₂) (zero_add 0)).comp
          e (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0) :=
        congrArg (fun x : Ext S'.X₁ Y 0 => x.comp (Ext.mk₀ b) (add_zero 0))
          (Ext.comp_assoc (Ext.mk₀ S'.f) (Ext.mk₀ φ.τ₂) e rfl rfl rfl).symm
      _ = (((Ext.mk₀ φ.τ₁).comp (Ext.mk₀ S.f) (zero_add 0)).comp
          e (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0) :=
        congrArg (fun x : Ext S'.X₁ S.X₂ 0 =>
          (x.comp e (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0)) h
      _ = _ :=
        congrArg (fun x : Ext S'.X₁ Y 0 => x.comp (Ext.mk₀ b) (add_zero 0))
          (Ext.comp_assoc (Ext.mk₀ φ.τ₁) (Ext.mk₀ S.f) e rfl rfl rfl)
  comm₂₃ := by
    apply AddCommGrpCat.ext
    intro e
    change hS'.extClass.comp
        (((Ext.mk₀ φ.τ₁).comp e (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0))
        (add_zero 1) =
      ((Ext.mk₀ φ.τ₃).comp (hS.extClass.comp e (add_zero 1))
        (zero_add 1)).comp (Ext.mk₀ b) (add_zero 1)
    calc
      _ = (hS'.extClass.comp ((Ext.mk₀ φ.τ₁).comp e (zero_add 0))
          (add_zero 1)).comp (Ext.mk₀ b) (add_zero 1) :=
        (Ext.comp_assoc hS'.extClass
          ((Ext.mk₀ φ.τ₁).comp e (zero_add 0)) (Ext.mk₀ b) rfl rfl rfl).symm
      _ = ((hS'.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1)).comp
          e (add_zero 1)).comp (Ext.mk₀ b) (add_zero 1) :=
        congrArg (fun x : Ext S'.X₃ Y 1 => x.comp (Ext.mk₀ b) (add_zero 1))
          (Ext.comp_assoc hS'.extClass (Ext.mk₀ φ.τ₁) e rfl rfl rfl).symm
      _ = (((Ext.mk₀ φ.τ₃).comp hS.extClass (zero_add 1)).comp
          e (add_zero 1)).comp (Ext.mk₀ b) (add_zero 1) :=
        congrArg (fun x : Ext S'.X₃ S.X₁ 1 =>
          (x.comp e (add_zero 1)).comp (Ext.mk₀ b) (add_zero 1))
          (hS'.extClass_naturality hS φ)
      _ = _ :=
        congrArg (fun x : Ext S'.X₃ Y 1 => x.comp (Ext.mk₀ b) (add_zero 1))
          (Ext.comp_assoc (Ext.mk₀ φ.τ₃) hS.extClass e rfl rfl rfl)

/-- The middle component retains the precomposition and postcomposition values. -/
lemma extPresentationMap_τ₂_apply (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') (e : Ext S.X₁ Y 0) :
    (hS.extPresentationMap hS' φ b).τ₂ e =
      ((Ext.mk₀ φ.τ₁).comp e (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0) := rfl

/-- The right component is the Ext action in both variables. -/
lemma extPresentationMap_τ₃_apply (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') (e : Ext S.X₃ Y 1) :
    (hS.extPresentationMap hS' φ b).τ₃ e =
      ((Ext.mk₀ φ.τ₃).comp e (zero_add 1)).comp (Ext.mk₀ b) (add_zero 1) := rfl

/-- The cokernel map is induced by the left square of the presentation map. -/
def extPresentationCokernelMap (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') :
    cokernel (hS.extPresentationSequence Y).f ⟶
      cokernel (hS'.extPresentationSequence Y').f :=
  cokernel.map _ _ (hS.extPresentationMap hS' φ b).τ₁
    (hS.extPresentationMap hS' φ b).τ₂
    (hS.extPresentationMap hS' φ b).comm₁₂.symm

/-- The cokernel comparison is simultaneously natural in the presentation and target. -/
lemma extPresentationCokernelIso_naturality (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') [Projective S.X₂] [Projective S'.X₂] :
    hS.extPresentationCokernelMap hS' φ b ≫
        (hS'.extPresentationCokernelIso Y').hom =
      (hS.extPresentationCokernelIso Y).hom ≫ (hS.extPresentationMap hS' φ b).τ₃ := by
  rw [extPresentationCokernelIso_hom, extPresentationCokernelIso_hom]
  exact cokernel.map_desc _ _ _ _ _ _
    (hS.extPresentationMap hS' φ b).τ₁ (hS.extPresentationMap hS' φ b).τ₂
    (hS.extPresentationMap hS' φ b).τ₃
    (hS.extPresentationMap hS' φ b).comm₁₂.symm
    (hS.extPresentationMap hS' φ b).comm₂₃.symm

end NativeExt

section OrdinaryHom

variable {S S' : ShortComplex C}

/-- Ordinary Hom precomposition by the given presentation arrow, with a canonical universe lift. -/
def homPresentationArrow (S : ShortComplex C) (Y : C) :
    liftedHom S.X₂ Y ⟶ liftedHom S.X₁ Y :=
  AddCommGrpCat.uliftFunctor.{u, v}.map ((preadditiveYoneda.obj Y).map S.f.op)

/-- A lifted ordinary morphism is precomposed by the arrow S.f. -/
lemma homPresentationArrow_apply (S : ShortComplex C) (Y : C)
    (k : ULift.{u, v} (S.X₂ ⟶ Y)) :
    homPresentationArrow S Y k = ULift.up (S.f ≫ k.down) := rfl

/-- The simultaneous Hom square induces this ordinary-presentation cokernel map. -/
def homPresentationCokernelMap (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') :
    cokernel (homPresentationArrow S Y) ⟶ cokernel (homPresentationArrow S' Y') :=
  cokernel.map _ _ (liftedHomMap φ.τ₂ b) (liftedHomMap φ.τ₁ b) (by
    apply AddCommGrpCat.ext
    intro k
    change ULift.up ((φ.τ₁ ≫ (S.f ≫ k.down)) ≫ b) =
      ULift.up (S'.f ≫ ((φ.τ₂ ≫ k.down) ≫ b))
    apply congrArg ULift.up
    simpa only [Category.assoc] using
      congrArg (fun t : S'.X₁ ⟶ S.X₂ => (t ≫ k.down) ≫ b) φ.comm₁₂)

/-- The degree-zero Ext equivalence identifies the lifted ordinary Hom group. -/
def homExtZeroIso (X Y : C) :
    letI := HasExt.standard C
    liftedHom X Y ≅ AddCommGrpCat.of (Ext.{max u v} X Y 0) := by
  letI := HasExt.standard C
  exact ((AddEquiv.ulift : ULift.{u, v} (X ⟶ Y) ≃+ (X ⟶ Y)).trans
    Ext.addEquiv₀.symm).toAddCommGrpIso

/-- The lifted ordinary representative maps to the degree-zero class. -/
lemma homExtZeroIso_hom_up (X Y : C) (k : X ⟶ Y) :
    letI := HasExt.standard C
    (homExtZeroIso X Y).hom (ULift.up k) = Ext.mk₀ k := rfl

/-- The cokernel of ordinary Hom precomposition computes Ext¹ using HasExt.standard. -/
def homPresentationCokernelIso (hS : S.ShortExact) (Y : C) [Projective S.X₂] :
    letI := HasExt.standard C
    cokernel (homPresentationArrow S Y) ≅ AddCommGrpCat.of (Ext.{max u v} S.X₃ Y 1) := by
  letI := HasExt.standard C
  refine cokernel.mapIso (homPresentationArrow S Y) (hS.extPresentationSequence Y).f
    (homExtZeroIso S.X₂ Y) (homExtZeroIso S.X₁ Y) ?_ ≪≫
      hS.extPresentationCokernelIso Y
  apply AddCommGrpCat.ext
  intro k
  change Ext.mk₀ (S.f ≫ k.down) =
    (Ext.mk₀ S.f).comp (Ext.mk₀ k.down) (zero_add 0)
  exact (Ext.mk₀_comp_mk₀ S.f k.down).symm

/-- The ordinary comparison descends the extension class after degree-zero conversion. -/
@[reassoc]
lemma homPresentationCokernelIso_π_hom (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] :
    letI := HasExt.standard C
    cokernel.π (homPresentationArrow S Y) ≫ (hS.homPresentationCokernelIso Y).hom =
      (homExtZeroIso S.X₁ Y).hom ≫ (hS.extPresentationSequence Y).g := by
  letI := HasExt.standard C
  let T : ShortComplex AddCommGrpCat.{max u v} := hS.extPresentationSequence Y
  let f : liftedHom S.X₂ Y ⟶ liftedHom S.X₁ Y := homPresentationArrow S Y
  let a : liftedHom S.X₂ Y ≅ T.X₁ := homExtZeroIso S.X₂ Y
  let b : liftedHom S.X₁ Y ≅ T.X₂ := homExtZeroIso S.X₁ Y
  have hSquare : f ≫ b.hom = a.hom ≫ T.f := by
    apply AddCommGrpCat.ext
    intro k
    change Ext.mk₀ (S.f ≫ k.down) =
      (Ext.mk₀ S.f).comp (Ext.mk₀ k.down) (zero_add 0)
    exact (Ext.mk₀_comp_mk₀ S.f k.down).symm
  let K : cokernel f ≅ cokernel T.f := cokernel.mapIso f T.f a b hSquare
  let E : cokernel T.f ≅ T.X₃ := hS.extPresentationCokernelIso Y
  have hPack : hS.homPresentationCokernelIso Y = K ≪≫ E := rfl
  have hπ : cokernel.π f ≫ K.hom = b.hom ≫ cokernel.π T.f := by
    dsimp only [K, cokernel.mapIso, cokernel.map]
    exact cokernel.π_desc _ _ _
  rw [hPack]
  change cokernel.π f ≫ (K.hom ≫ E.hom) = b.hom ≫ T.g
  calc
    _ = (cokernel.π f ≫ K.hom) ≫ E.hom := (Category.assoc _ _ _).symm
    _ = (b.hom ≫ cokernel.π T.f) ≫ E.hom := congrArg (fun k => k ≫ E.hom) hπ
    _ = b.hom ≫ (cokernel.π T.f ≫ E.hom) := Category.assoc _ _ _
    _ = _ := congrArg (fun k => b.hom ≫ k) (hS.extPresentationCokernelIso_π_hom Y)

/-- The ordinary cokernel representative is sent to its Yoneda pushout class. -/
lemma homPresentationCokernelIso_apply (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] (k : S.X₁ ⟶ Y) :
    letI := HasExt.standard C
    (hS.homPresentationCokernelIso Y).hom
      (cokernel.π (homPresentationArrow S Y) (ULift.up k)) =
        hS.extClass.comp (Ext.mk₀ k) (add_zero 1) := by
  letI := HasExt.standard C
  exact ConcreteCategory.congr_hom (hS.homPresentationCokernelIso_π_hom Y) (ULift.up k)

/-- The inverse comparison represents the same extension class in the Hom cokernel. -/
lemma homPresentationCokernelIso_inv_extClass_comp_mk₀ (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] (k : S.X₁ ⟶ Y) :
    letI := HasExt.standard C
    (hS.homPresentationCokernelIso Y).inv
      (hS.extClass.comp (Ext.mk₀ k) (add_zero 1)) =
        cokernel.π (homPresentationArrow S Y) (ULift.up k) := by
  letI := HasExt.standard C
  rw [← hS.homPresentationCokernelIso_apply Y k]
  exact ConcreteCategory.congr_hom (hS.homPresentationCokernelIso Y).hom_inv_id _

/-- The ordinary Hom cokernel comparison is natural in both variables. -/
lemma homPresentationCokernelIso_naturality (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') [Projective S.X₂] [Projective S'.X₂] :
    letI := HasExt.standard C
    homPresentationCokernelMap φ b ≫ (hS'.homPresentationCokernelIso Y').hom =
      (hS.homPresentationCokernelIso Y).hom ≫
        ((extFunctor 1).map φ.τ₃.op).app Y ≫ (extFunctorObj S'.X₃ 1).map b := by
  letI := HasExt.standard C
  let T : ShortComplex AddCommGrpCat.{max u v} := hS.extPresentationSequence Y
  let T' : ShortComplex AddCommGrpCat.{max u v} := hS'.extPresentationSequence Y'
  let m : T ⟶ T' := hS.extPresentationMap hS' φ b
  let f : liftedHom S.X₂ Y ⟶ liftedHom S.X₁ Y := homPresentationArrow S Y
  let f' : liftedHom S'.X₂ Y' ⟶ liftedHom S'.X₁ Y' := homPresentationArrow S' Y'
  let c : cokernel f ⟶ cokernel f' := homPresentationCokernelMap φ b
  let E : cokernel f ≅ T.X₃ := hS.homPresentationCokernelIso Y
  let E' : cokernel f' ≅ T'.X₃ := hS'.homPresentationCokernelIso Y'
  let a : liftedHom S.X₁ Y ≅ T.X₂ := homExtZeroIso S.X₁ Y
  let a' : liftedHom S'.X₁ Y' ≅ T'.X₂ := homExtZeroIso S'.X₁ Y'
  let l : liftedHom S.X₁ Y ⟶ liftedHom S'.X₁ Y' := liftedHomMap φ.τ₁ b
  have hZero : l ≫ a'.hom = a.hom ≫ m.τ₂ := by
    apply AddCommGrpCat.ext
    intro k
    have hk : a.hom k = Ext.mk₀ k.down := homExtZeroIso_hom_up S.X₁ Y k.down
    have hl : l k = ULift.up ((φ.τ₁ ≫ k.down) ≫ b) := liftedHomMap_apply φ.τ₁ b k
    have hMk : Ext.mk₀ ((φ.τ₁ ≫ k.down) ≫ b) =
        ((Ext.mk₀ φ.τ₁).comp (Ext.mk₀ k.down) (zero_add 0)).comp
          (Ext.mk₀ b) (add_zero 0) :=
      (Ext.mk₀_comp_mk₀ (φ.τ₁ ≫ k.down) b).symm.trans
        (congrArg (fun x : Ext S'.X₁ Y 0 => x.comp (Ext.mk₀ b) (add_zero 0))
          (Ext.mk₀_comp_mk₀ φ.τ₁ k.down).symm)
    have ha' : a'.hom (ULift.up ((φ.τ₁ ≫ k.down) ≫ b)) =
        (Ext.mk₀ ((φ.τ₁ ≫ k.down) ≫ b) : Ext.{max u v} S'.X₁ Y' 0) :=
      homExtZeroIso_hom_up S'.X₁ Y' ((φ.τ₁ ≫ k.down) ≫ b)
    have hComponent :
        ((Ext.mk₀ φ.τ₁).comp (Ext.mk₀ k.down) (zero_add 0)).comp
          (Ext.mk₀ b) (add_zero 0) = m.τ₂ (Ext.mk₀ k.down) :=
      (hS.extPresentationMap_τ₂_apply hS' φ b (Ext.mk₀ k.down)).symm
    have hLeft : (l ≫ a'.hom) k = a'.hom (l k) :=
      AddCommGrpCat.comp_apply l a'.hom k
    have hRight : m.τ₂ (a.hom k) = (a.hom ≫ m.τ₂) k :=
      (AddCommGrpCat.comp_apply a.hom m.τ₂ k).symm
    exact hLeft.trans ((congrArg a'.hom hl).trans
      (ha'.trans (hMk.trans (hComponent.trans ((congrArg m.τ₂ hk.symm).trans hRight)))))
  have hπMap : cokernel.π f ≫ c = l ≫ cokernel.π f' := by
    dsimp only [c, f, f', l, homPresentationCokernelMap, cokernel.map]
    exact cokernel.π_desc _ _ _
  have hπ : cokernel.π f ≫ E.hom = a.hom ≫ T.g :=
    hS.homPresentationCokernelIso_π_hom Y
  have hπ' : cokernel.π f' ≫ E'.hom = a'.hom ≫ T'.g :=
    hS'.homPresentationCokernelIso_π_hom Y'
  change c ≫ E'.hom = E.hom ≫ m.τ₃
  apply (cancel_epi (cokernel.π f)).1
  calc
    _ = (cokernel.π f ≫ c) ≫ E'.hom := (Category.assoc _ _ _).symm
    _ = (l ≫ cokernel.π f') ≫ E'.hom := congrArg (fun k => k ≫ E'.hom) hπMap
    _ = l ≫ (cokernel.π f' ≫ E'.hom) := Category.assoc _ _ _
    _ = l ≫ (a'.hom ≫ T'.g) := congrArg (fun k => l ≫ k) hπ'
    _ = (l ≫ a'.hom) ≫ T'.g := (Category.assoc _ _ _).symm
    _ = (a.hom ≫ m.τ₂) ≫ T'.g := congrArg (fun k => k ≫ T'.g) hZero
    _ = a.hom ≫ (m.τ₂ ≫ T'.g) := Category.assoc _ _ _
    _ = a.hom ≫ (T.g ≫ m.τ₃) := congrArg (fun k => a.hom ≫ k) m.comm₂₃
    _ = (a.hom ≫ T.g) ≫ m.τ₃ := (Category.assoc _ _ _).symm
    _ = (cokernel.π f ≫ E.hom) ≫ m.τ₃ :=
      congrArg (fun k => k ≫ m.τ₃) hπ.symm
    _ = _ := Category.assoc _ _ _

end OrdinaryHom

end ShortComplex.ShortExact

end CategoryTheory
