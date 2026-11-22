/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarSM7
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Raw mapping support for the original injective Kan model

The actual initial and terminal mapping ends identify every supplied end
pullback corner with the original precomposition or postcomposition arrow.
Their two original projections remain visible. The selected model's scalar
SM7 and native Brown theorem then give raw Kan fibrancy and weak invariance
in both original variables, including nonmonic weak source arrows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The actual end out of the original initial presheaf is terminal. -/
def initialEndIsTerminal (Z : SimplicialPresheaf.{u} D) :
    IsTerminal (innerHom (⊥_ SimplicialPresheaf.{u} D) Z) := by
  have hi (K : SSet.{u}) :
      IsInitial ((scalarTensor.obj (⊥_ SimplicialPresheaf.{u} D)).obj K) := by
    let : (scalarTensorFixed (D := D) K).IsLeftAdjoint :=
      (scalarTensorCotensorAdjunction (D := D) K).isLeftAdjoint
    exact initialIsInitial.isInitialObj (scalarTensorFixed (D := D) K) _
  refine IsTerminal.ofUniqueHom
    (fun K => scalarTensorHomEquiv _ K Z ((hi K).to Z)) ?_
  intro K m
  apply (scalarTensorHomEquiv (⊥_ SimplicialPresheaf.{u} D) K Z).symm.injective
  rw [Equiv.symm_apply_apply]
  exact (hi K).hom_ext _ _

/-- The actual end into the original terminal presheaf is terminal. -/
def terminalEndIsTerminal (A : SimplicialPresheaf.{u} D) :
    IsTerminal (innerHom A (⊤_ SimplicialPresheaf.{u} D)) := by
  let : (innerHomFunctor.obj (op A)).IsRightAdjoint :=
    (scalarTensorHomAdjunction A).isRightAdjoint
  exact terminalIsTerminal.isTerminalObj (innerHomFunctor.obj (op A)) _

private theorem terminalCorner_fst_isIso {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (q : innerHomFunctor.PullbackObjObj i (terminal.from Z)) : IsIso q.fst := by
  let : IsIso ((innerHomFunctor.map i.op).app (⊤_ SimplicialPresheaf.{u} D)) :=
    isIso_of_isTerminal (terminalEndIsTerminal B) (terminalEndIsTerminal A) _
  exact q.isPullback.isIso_fst_of_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Every supplied terminal end corner is the whole original precomposition arrow. -/
def precompCornerIso {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (q : innerHomFunctor.PullbackObjObj i (terminal.from Z)) :
    Arrow.mk q.π ≅ Arrow.mk (innerHomPre i Z) := by
  let : IsIso q.fst := terminalCorner_fst_isIso i Z q
  refine Arrow.isoMk (Iso.refl _) (asIso q.fst) ?_
  change 𝟙 (innerHom B Z) ≫ innerHomPre i Z = q.π ≫ q.fst
  rw [Category.id_comp]
  exact q.π_fst.symm

/-- Both left-object maps of the supplied terminal-corner comparison are original identities. -/
theorem precompCornerIso_left {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (q : innerHomFunctor.PullbackObjObj i (terminal.from Z)) :
    (precompCornerIso i Z q).hom.left = 𝟙 (innerHom B Z) ∧
      (precompCornerIso i Z q).inv.left = 𝟙 (innerHom B Z) := by
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The forward terminal-corner map is the original chosen first projection. -/
theorem precompCornerIso_hom_right {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (q : innerHomFunctor.PullbackObjObj i (terminal.from Z)) :
    (precompCornerIso i Z q).hom.right = q.fst := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse terminal-corner map retains both original prescribed projections. -/
theorem precompCornerIso_inv_projections {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (q : innerHomFunctor.PullbackObjObj i (terminal.from Z)) :
    (precompCornerIso i Z q).inv.right ≫ q.fst = 𝟙 (innerHom A Z) ∧
      (precompCornerIso i Z q).inv.right ≫ q.snd =
        (terminalEndIsTerminal B).from (innerHom A Z) := by
  let : IsIso q.fst := terminalCorner_fst_isIso i Z q
  constructor
  · exact IsIso.inv_hom_id q.fst
  · exact (terminalEndIsTerminal B).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- Both whole terminal-corner Arrow equations retain the original structural map. -/
theorem precompCornerIso_fac {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (q : innerHomFunctor.PullbackObjObj i (terminal.from Z)) :
    q.π ≫ (precompCornerIso i Z q).hom.right = innerHomPre i Z ∧
      innerHomPre i Z ≫ (precompCornerIso i Z q).inv.right = q.π := by
  constructor
  · rw [precompCornerIso_hom_right]
    exact q.π_fst
  · let : IsIso q.fst := terminalCorner_fst_isIso i Z q
    change (innerHomFunctor.map i.op).app Z ≫ inv q.fst = q.π
    rw [← q.π_fst, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem initialCorner_snd_isIso (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (q : innerHomFunctor.PullbackObjObj (initial.to A) p) : IsIso q.snd := by
  let : IsIso ((innerHomFunctor.obj (op (⊥_ SimplicialPresheaf.{u} D))).map p) :=
    isIso_of_isTerminal (initialEndIsTerminal X) (initialEndIsTerminal Y) _
  exact q.isPullback.isIso_snd_of_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Every supplied initial end corner is the whole original postcomposition arrow. -/
def postcompCornerIso (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (q : innerHomFunctor.PullbackObjObj (initial.to A) p) :
    Arrow.mk q.π ≅ Arrow.mk (innerHomPost A p) := by
  let : IsIso q.snd := initialCorner_snd_isIso A p q
  refine Arrow.isoMk (Iso.refl _) (asIso q.snd) ?_
  change 𝟙 (innerHom A X) ≫ innerHomPost A p = q.π ≫ q.snd
  rw [Category.id_comp]
  exact q.π_snd.symm

/-- Both left-object maps of the supplied initial-corner comparison are original identities. -/
theorem postcompCornerIso_left (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (q : innerHomFunctor.PullbackObjObj (initial.to A) p) :
    (postcompCornerIso A p q).hom.left = 𝟙 (innerHom A X) ∧
      (postcompCornerIso A p q).inv.left = 𝟙 (innerHom A X) := by
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The forward initial-corner map is the original chosen second projection. -/
theorem postcompCornerIso_hom_right (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (q : innerHomFunctor.PullbackObjObj (initial.to A) p) :
    (postcompCornerIso A p q).hom.right = q.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse initial-corner map retains both original prescribed projections. -/
theorem postcompCornerIso_inv_projections (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (q : innerHomFunctor.PullbackObjObj (initial.to A) p) :
    (postcompCornerIso A p q).inv.right ≫ q.fst =
        (initialEndIsTerminal X).from (innerHom A Y) ∧
      (postcompCornerIso A p q).inv.right ≫ q.snd = 𝟙 (innerHom A Y) := by
  let : IsIso q.snd := initialCorner_snd_isIso A p q
  constructor
  · exact (initialEndIsTerminal X).hom_ext _ _
  · exact IsIso.inv_hom_id q.snd

set_option backward.isDefEq.respectTransparency false in
/-- Both whole initial-corner Arrow equations retain the original structural map. -/
theorem postcompCornerIso_fac (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (q : innerHomFunctor.PullbackObjObj (initial.to A) p) :
    q.π ≫ (postcompCornerIso A p q).hom.right = innerHomPost A p ∧
      innerHomPost A p ≫ (postcompCornerIso A p q).inv.right = q.π := by
  constructor
  · rw [postcompCornerIso_hom_right]
    exact q.π_snd
  · let : IsIso q.snd := initialCorner_snd_isIso A p q
    change (innerHomFunctor.obj (op A)).map p ≫ inv q.snd = q.π
    rw [← q.π_snd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Original cofibrations induce raw Kan fibrations into an actual fibrant target. -/
theorem rawPrecomp_fibration_of_cofibration {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i) (hZ : IsFibrant Z) :
    fibrations SSet.{u} (innerHomPre i Z) := by
  let : IsFibrant Z := hZ
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor i (terminal.from Z)
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff (precompCornerIso i Z q)).mp
    (scalar_pullbackObjObj_fibration i (terminal.from Z) q hi (mem_fibrations _))

/-- Original trivial cofibrations induce raw trivial fibrations into an actual fibrant target. -/
theorem rawPrecomp_trivialFibration_of_trivialCofibration
    {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (hi : trivialCofibrations (SimplicialPresheaf.{u} D) i) (hZ : IsFibrant Z) :
    trivialFibrations SSet.{u} (innerHomPre i Z) := by
  let : IsFibrant Z := hZ
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor i (terminal.from Z)
  exact ((trivialFibrations SSet.{u}).arrow_mk_iso_iff (precompCornerIso i Z q)).mp
    (scalar_pullbackObjObj_trivialFibration_of_left i (terminal.from Z) q hi
      (mem_fibrations _))

/-- Every global original fibration induces a raw Kan fibration from any original source. -/
theorem rawPostcomp_fibration_of_fibration (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : fibrations (SimplicialPresheaf.{u} D) p) :
    fibrations SSet.{u} (innerHomPost A p) := by
  let : IsCofibrant A := (data D).all_cofibrant A
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor (initial.to A) p
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff (postcompCornerIso A p q)).mp
    (scalar_pullbackObjObj_fibration (initial.to A) p q (mem_cofibrations _) hp)

/-- Every global original trivial fibration induces a raw trivial fibration from any source. -/
theorem rawPostcomp_trivialFibration_of_trivialFibration (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : trivialFibrations (SimplicialPresheaf.{u} D) p) :
    trivialFibrations SSet.{u} (innerHomPost A p) := by
  let : IsCofibrant A := (data D).all_cofibrant A
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor (initial.to A) p
  exact ((trivialFibrations SSet.{u}).arrow_mk_iso_iff (postcompCornerIso A p q)).mp
    (scalar_pullbackObjObj_trivialFibration_of_right (initial.to A) p q
      (mem_cofibrations _) hp)

/-- The actual mapping end into an injectively fibrant target is Kan at every original source. -/
theorem innerHom_isFibrant (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    IsFibrant (innerHom A Z) := by
  let : IsCofibrant A := (data D).all_cofibrant A
  have hp : Fibration (innerHomPre (initial.to A) Z) :=
    (fibration_iff _).mpr
      (rawPrecomp_fibration_of_cofibration (initial.to A) Z (mem_cofibrations _) hZ)
  exact (isFibrant_iff_of_isTerminal (innerHomPre (initial.to A) Z)
    (initialEndIsTerminal Z)).mpr hp

private theorem opposite_isFibrant (A : SimplicialPresheaf.{u} D) : IsFibrant (op A) := by
  let : IsCofibrant A := (data D).all_cofibrant A
  exact (isFibrant_iff_of_isTerminal (initial.to A).op initialIsInitial.op).mpr
    (by infer_instance)

private theorem scalar_iso_weak :
    isomorphisms SSet.{u} ≤ SSet.realizationWeakEquivalences.{u} := by
  intro X Y f hf
  let : IsIso f := hf
  exact mem_weakEquivalences f

/-- Every original weak source map induces a raw weak map into an actual fibrant target. -/
theorem innerHomPre_weak_of_weakEquivalence {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (hf : weakEquivalences (SimplicialPresheaf.{u} D) f) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (innerHomPre f Z) := by
  let : IsFibrant (op A) := opposite_isFibrant A
  let : IsFibrant (op B) := opposite_isFibrant B
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  exact Functor.map_mem_of_weakEquivalence_of_fibrant (innerHomFunctor.flip.obj Z)
    SSet.realizationWeakEquivalences scalar_iso_weak (by
      intro X Y p _ _ hp
      have ht : trivialCofibrations (SimplicialPresheaf.{u} D) p.unop := by
        simpa only [trivialFibrations_op, MorphismProperty.op] using hp
      exact (rawPrecomp_trivialFibration_of_trivialCofibration p.unop Z ht hZ).2) f.op

/-- Every original weak map between actual fibrant targets induces a raw weak target map. -/
theorem innerHomPost_weak_of_weakEquivalence (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : weakEquivalences (SimplicialPresheaf.{u} D) p)
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    SSet.realizationWeakEquivalences (innerHomPost A p) := by
  let : IsFibrant X := hX
  let : IsFibrant Y := hY
  let : WeakEquivalence p := (weakEquivalence_iff _).mpr hp
  exact Functor.map_mem_of_weakEquivalence_of_fibrant (innerHomFunctor.obj (op A))
    SSet.realizationWeakEquivalences scalar_iso_weak (by
      intro U V f _ _ hf
      exact (rawPostcomp_trivialFibration_of_trivialFibration A f hf).2) p

/-- All seven raw class, Kan and arbitrary weak-invariance clauses for the actual original model. -/
theorem rawMappingInvariance (D : Type w) [Category.{v} D] [Small.{u} D]
    [LocallySmall.{u} D] :
    (∀ {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D),
      cofibrations (SimplicialPresheaf.{u} D) i → IsFibrant Z →
        fibrations SSet.{u} (innerHomPre i Z)) ∧
    (∀ {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) (Z : SimplicialPresheaf.{u} D),
      trivialCofibrations (SimplicialPresheaf.{u} D) i → IsFibrant Z →
        trivialFibrations SSet.{u} (innerHomPre i Z)) ∧
    (∀ (A : SimplicialPresheaf.{u} D) {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y),
      fibrations (SimplicialPresheaf.{u} D) p → fibrations SSet.{u} (innerHomPost A p)) ∧
    (∀ (A : SimplicialPresheaf.{u} D) {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y),
      trivialFibrations (SimplicialPresheaf.{u} D) p →
        trivialFibrations SSet.{u} (innerHomPost A p)) ∧
    (∀ A Z : SimplicialPresheaf.{u} D, IsFibrant Z → IsFibrant (innerHom A Z)) ∧
    (∀ {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D),
      weakEquivalences (SimplicialPresheaf.{u} D) f → IsFibrant Z →
        SSet.realizationWeakEquivalences (innerHomPre f Z)) ∧
    (∀ (A : SimplicialPresheaf.{u} D) {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y),
      weakEquivalences (SimplicialPresheaf.{u} D) p → IsFibrant X → IsFibrant Y →
        SSet.realizationWeakEquivalences (innerHomPost A p)) := by
  exact ⟨rawPrecomp_fibration_of_cofibration,
    rawPrecomp_trivialFibration_of_trivialCofibration,
    rawPostcomp_fibration_of_fibration, rawPostcomp_trivialFibration_of_trivialFibration,
    innerHom_isFibrant, innerHomPre_weak_of_weakEquivalence,
    innerHomPost_weak_of_weakEquivalence⟩

end SimplicialPresheaf.InjectiveKan
