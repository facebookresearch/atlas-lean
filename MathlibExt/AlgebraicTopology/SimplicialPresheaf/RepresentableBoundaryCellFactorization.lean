/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.FreeRepresentableCells
import MathlibExt.CategoryTheory.SmallObject.DiagramEligibility
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPSimplicialHomotopyEquiv

/-!
# Original representable-boundary cells and their functorial factorization

The fixed native small-object construction is recoded by whole Arrow
isomorphisms to the original representable scalar boundaries. Its entire
ordinal chain and coproduct attachment data are retained. The initial-arrow
construction gives a functorial replacement with an objectwise weak augmentation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType SimplicialPresheaf.freeEvaluationHomCoproducts

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D] [LocallySmall.{u} D]

/-- The original free images of every actual scalar boundary member. -/
def projectiveBoundaryMaps : MorphismProperty (SimplicialPresheaf.{u} D) :=
  MorphismProperty.adjointFamilyGenerators
    (fun e : Dᵒᵖ => freeEvaluationFunctor.obj e.unop) SSet.modelCategoryQuillen.I.{u}

/-- The literal original representable tensor of a scalar boundary inclusion. -/
def representableBoundaryCell (dn : D × ℕ) :
    (scalarTensor.obj (discreteYoneda.obj dn.1)).obj (SSet.boundary.{u} dn.2) ⟶
      (scalarTensor.obj (discreteYoneda.obj dn.1)).obj
        (Arrow.mk (SSet.boundary.{u} dn.2).ι).right :=
  (scalarTensor.obj (discreteYoneda.obj dn.1)).map (SSet.boundary.{u} dn.2).ι

variable [Small.{u} D]


/-- The same native free-boundary factorization, fixed at the original aleph-zero. -/
def representableBoundaryFactorization :
    MorphismProperty.FunctorialFactorizationData (projectiveBoundaryMaps (D := D)).rlp.llp
        (projectiveBoundaryMaps (D := D)).rlp := by
  letI : (projectiveBoundaryMaps (D := D)).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
      (isCardinalForSmallObjectArgument_freeDiagrams (J := Dᵒᵖ)
    SSet.modelCategoryQuillen.I.{u} Cardinal.aleph0.{u}
    SSet.modelCategoryQuillen.instIsCardinalForSmallObjectArgumentIAleph0_mathlibExt)
  exact SmallObject.functorialFactorizationData
      (projectiveBoundaryMaps (D := D)) Cardinal.aleph0.{u}


/-- Recode only actual native cell labels and keep the complete original chain. -/
def representableBoundaryFactorizationCells (f : Arrow (SimplicialPresheaf.{u} D)) :
    RelativeCellComplex.{u} (fun (_ : (Cardinal.aleph0.{u}).ord.ToType) =>
        representableBoundaryCell (D := D))
      ((representableBoundaryFactorization (D := D)).i.app f) := by
  letI : (projectiveBoundaryMaps (D := D)).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
      (isCardinalForSmallObjectArgument_freeDiagrams (J := Dᵒᵖ)
    SSet.modelCategoryQuillen.I.{u} Cardinal.aleph0.{u}
    SSet.modelCategoryQuillen.instIsCardinalForSmallObjectArgumentIAleph0_mathlibExt)
  let c₀ := SmallObject.relativeCellComplexιObj
      (projectiveBoundaryMaps (D := D)) Cardinal.aleph0.{u} f.hom
  let c₁ := c₀.adjointFamilyCellTypes
    (fun e : Dᵒᵖ => freeEvaluationFunctor.obj e.unop) SSet.modelCategoryQuillen.I.{u}
  let witness (p : SSet.modelCategoryQuillen.I.{u}.toSet) :
      ∃ n : ℕ, Arrow.mk p.1.hom = Arrow.mk (SSet.boundary.{u} n).ι :=
    (MorphismProperty.ofHoms_iff
      (fun n : ℕ => (SSet.boundary.{u} n).ι) p.1.hom).mp p.2
  let dim (p : SSet.modelCategoryQuillen.I.{u}.toSet) : ℕ := (witness p).choose
  let label (q : Dᵒᵖ × SSet.modelCategoryQuillen.I.{u}.toSet) : D × ℕ :=
    (q.1.unop, dim q.2)
  let e (q : Dᵒᵖ × SSet.modelCategoryQuillen.I.{u}.toSet) :
      Arrow.mk ((freeEvaluationFunctor.obj q.1.unop).map q.2.1.hom) ≅
        Arrow.mk (representableBoundaryCell (label q)) :=
    (freeEvaluationFunctor.obj q.1.unop).mapArrow.mapIso
        (eqToIso (witness q.2).choose_spec) ≪≫
      freeScalarArrowIso q.1.unop (SSet.boundary.{u} (dim q.2)).ι
  exact
    { toTransfiniteCompositionOfShape := c₁.toTransfiniteCompositionOfShape
      attachCells j hj := (c₁.attachCells j hj).reindexCellTypes
        (representableBoundaryCell (D := D)) label e }

/-- The recoded witness has exactly the native stages, inclusions and colimit data. -/
theorem representableBoundaryFactorization_cells_geometry
    (f : Arrow (SimplicialPresheaf.{u} D)) :
    letI : (projectiveBoundaryMaps (D := D)).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
        (isCardinalForSmallObjectArgument_freeDiagrams (J := Dᵒᵖ)
    SSet.modelCategoryQuillen.I.{u} Cardinal.aleph0.{u}
    SSet.modelCategoryQuillen.instIsCardinalForSmallObjectArgumentIAleph0_mathlibExt)
    (representableBoundaryFactorizationCells f).toTransfiniteCompositionOfShape =
      (SmallObject.relativeCellComplexιObj (projectiveBoundaryMaps (D := D))
        Cardinal.aleph0.{u} f.hom).toTransfiniteCompositionOfShape := rfl

/-- Every original successor is the pushout of the actual coproduct of literal cells. -/
theorem representableBoundaryFactorization_step
    (f : Arrow (SimplicialPresheaf.{u} D)) (j : (Cardinal.aleph0.{u}).ord.ToType) (hj : ¬ IsMax j) :
    let c := representableBoundaryFactorizationCells f
    let a := c.attachCells j hj
    let A := fun s : a.ι => (Arrow.mk (representableBoundaryCell (a.π s))).left
    let B := fun s : a.ι => (Arrow.mk (representableBoundaryCell (a.π s))).right
    ∃ (eL : (∐ A) ≅ a.cofan₁.pt) (eR : (∐ B) ≅ a.cofan₂.pt),
      (∀ s, Sigma.ι A s ≫ eL.hom = a.cofan₁.inj s) ∧
      (∀ s, a.cofan₁.inj s ≫ eL.inv = Sigma.ι A s) ∧
      (∀ s, Sigma.ι B s ≫ eR.hom = a.cofan₂.inj s) ∧
      (∀ s, a.cofan₂.inj s ≫ eR.inv = Sigma.ι B s) ∧
      (CategoryTheory.Limits.Sigma.map (fun s => representableBoundaryCell (a.π s)) ≫ eR.hom =
        eL.hom ≫ a.m) ∧
      IsPushout (eL.hom ≫ a.g₁) (CategoryTheory.Limits.Sigma.map
          (fun s => representableBoundaryCell (a.π s)))
        (c.F.map (homOfLE (Order.le_succ j))) (eR.hom ≫ a.g₂) ∧
      (eL.hom ≫ a.g₁) ≫ c.F.map (homOfLE (Order.le_succ j)) =
        CategoryTheory.Limits.Sigma.map (fun s => representableBoundaryCell (a.π s)) ≫
            (eR.hom ≫ a.g₂) := by
  let c := representableBoundaryFactorizationCells f
  let a := c.attachCells j hj
  let A := fun s : a.ι => (Arrow.mk (representableBoundaryCell (a.π s))).left
  let B := fun s : a.ι => (Arrow.mk (representableBoundaryCell (a.π s))).right
  let eL : (∐ A) ≅ a.cofan₁.pt :=
    IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct A) a.isColimit₁
  let eR : (∐ B) ≅ a.cofan₂.pt :=
    IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct B) a.isColimit₂
  have hL (s : a.ι) : Sigma.ι A s ≫ eL.hom = a.cofan₁.inj s := by
    simpa [eL, Cofan.inj] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct A) a.isColimit₁ (Discrete.mk s)
  have hLi (s : a.ι) : a.cofan₁.inj s ≫ eL.inv = Sigma.ι A s := by
    simp [eL, Cofan.inj]
  have hR (s : a.ι) : Sigma.ι B s ≫ eR.hom = a.cofan₂.inj s := by
    simpa [eR, Cofan.inj] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct B) a.isColimit₂ (Discrete.mk s)
  have hRi (s : a.ι) : a.cofan₂.inj s ≫ eR.inv = Sigma.ι B s := by
    simp [eR, Cofan.inj]
  have hm : CategoryTheory.Limits.Sigma.map (fun s => representableBoundaryCell (a.π s)) ≫ eR.hom =
      eL.hom ≫ a.m := by
    apply Sigma.hom_ext
    intro s
    rw [← Category.assoc, Sigma.ι_map, Category.assoc]
    change representableBoundaryCell (a.π s) ≫ (Sigma.ι B s ≫ eR.hom) =
      Sigma.ι A s ≫ (eL.hom ≫ a.m)
    rw [hR, ← Category.assoc, hL, a.hm]
  have sq : IsPushout (eL.hom ≫ a.g₁)
      (CategoryTheory.Limits.Sigma.map (fun s => representableBoundaryCell (a.π s)))
      (c.F.map (homOfLE (Order.le_succ j))) (eR.hom ≫ a.g₂) := by
    apply a.isPushout.of_iso eL.symm (Iso.refl _) eR.symm (Iso.refl _)
    · simp
    · rw [← cancel_mono eR.hom]
      simp [Category.assoc, hm]
    · simp
    · simp
  exact ⟨eL, eR, hL, hLi, hR, hRi, hm, sq, sq.w⟩

/-- Whole Arrow maps retain both factors and every original stage/cocone square. -/
theorem representableBoundaryFactorization_maps
    {f g h : Arrow (SimplicialPresheaf.{u} D)} (t : f ⟶ g) (s : g ⟶ h) :
    let : (projectiveBoundaryMaps (D := D)).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
        (isCardinalForSmallObjectArgument_freeDiagrams (J := Dᵒᵖ)
    SSet.modelCategoryQuillen.I.{u} Cardinal.aleph0.{u}
    SSet.modelCategoryQuillen.instIsCardinalForSmallObjectArgumentIAleph0_mathlibExt)
    let it := SmallObject.iterationFunctor (projectiveBoundaryMaps (D := D)) Cardinal.aleph0.{u}
    (representableBoundaryFactorization (D := D)).i.app f ≫
        (representableBoundaryFactorization (D := D)).p.app f = f.hom ∧
      (representableBoundaryFactorization (D := D)).i.app f ≫
          (representableBoundaryFactorization (D := D)).Z.map t = t.left ≫
          (representableBoundaryFactorization (D := D)).i.app g ∧
      (representableBoundaryFactorization (D := D)).Z.map t ≫
          (representableBoundaryFactorization (D := D)).p.app g =
          (representableBoundaryFactorization (D := D)).p.app f ≫ t.right ∧
      (representableBoundaryFactorization (D := D)).Z.map (𝟙 f) =
          𝟙 ((representableBoundaryFactorization (D := D)).Z.obj f) ∧
      (representableBoundaryFactorization (D := D)).Z.map (t ≫ s) =
          (representableBoundaryFactorization (D := D)).Z.map t ≫
          (representableBoundaryFactorization (D := D)).Z.map s ∧
      (∀ (j k : (Cardinal.aleph0.{u}).ord.ToType) (hjk : j ≤ k),
        (representableBoundaryFactorizationCells f).F.map (homOfLE hjk) ≫
            ((it.obj k).map t).left =
          ((it.obj j).map t).left ≫
            (representableBoundaryFactorizationCells g).F.map (homOfLE hjk)) ∧
      (∀ j : (Cardinal.aleph0.{u}).ord.ToType,
          (representableBoundaryFactorizationCells f).incl.app j ≫
          (representableBoundaryFactorization (D := D)).Z.map t =
        ((it.obj j).map t).left ≫
          (representableBoundaryFactorizationCells g).incl.app j) ∧
      (∀ j : (Cardinal.aleph0.{u}).ord.ToType,
          ((it.obj j).map (𝟙 f)).left = 𝟙 (((it.obj j).obj f).left)) ∧
      (∀ j : (Cardinal.aleph0.{u}).ord.ToType, ((it.obj j).map (t ≫ s)).left =
        ((it.obj j).map t).left ≫ ((it.obj j).map s).left) := by
  let : (projectiveBoundaryMaps (D := D)).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} :=
      (isCardinalForSmallObjectArgument_freeDiagrams (J := Dᵒᵖ)
    SSet.modelCategoryQuillen.I.{u} Cardinal.aleph0.{u}
    SSet.modelCategoryQuillen.instIsCardinalForSmallObjectArgumentIAleph0_mathlibExt)
  let it := SmallObject.iterationFunctor (projectiveBoundaryMaps (D := D)) Cardinal.aleph0.{u}
  refine ⟨(representableBoundaryFactorization (D := D)).fac_app,
      ((representableBoundaryFactorization (D := D)).i.naturality t).symm,
      (representableBoundaryFactorization (D := D)).p.naturality t,
    (representableBoundaryFactorization (D := D)).Z.map_id f,
        (representableBoundaryFactorization (D := D)).Z.map_comp t s, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    exact (Arrow.leftFunc.congr_map ((it.map (homOfLE hjk)).naturality t)).symm
  · intro j
    exact (Arrow.leftFunc.congr_map
      (((SmallObject.transfiniteCompositionOfShapeSuccStructPropιIteration
        (projectiveBoundaryMaps (D := D)) Cardinal.aleph0.{u}).incl.app j).naturality t)).symm
  · intro j
    simp
  · intro j
    simp

/-- The original right class equals both literal cell RLP and pointwise scalar boundary RLP. -/
theorem representableBoundaryFactorization_pointwise
    (f : Arrow (SimplicialPresheaf.{u} D)) :
    (projectiveBoundaryMaps (D := D)).rlp =
        (MorphismProperty.ofHoms (representableBoundaryCell (D := D))).rlp ∧
      (projectiveBoundaryMaps (D := D)).rlp =
          (SSet.modelCategoryQuillen.I.{u}.rlp).functorCategory Dᵒᵖ ∧
      (SSet.modelCategoryQuillen.I.{u}.rlp).functorCategory Dᵒᵖ
          ((representableBoundaryFactorization (D := D)).p.app f) ∧
      SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ
          ((representableBoundaryFactorization (D := D)).p.app f) := by
  have he : (projectiveBoundaryMaps (D := D)).rlp =
      (SSet.modelCategoryQuillen.I.{u}.rlp).functorCategory Dᵒᵖ := by
    ext X Y a
    exact MorphismProperty.adjointFamilyGenerators_rlp_iff
      (fun e : Dᵒᵖ => freeEvaluationFunctor.obj e.unop)
      (fun e : Dᵒᵖ => (evaluation Dᵒᵖ SSet.{u}).obj e)
      (fun e : Dᵒᵖ => evaluationAdjunctionRight SSet.{u} e)
      SSet.modelCategoryQuillen.I.{u} a
  have hl : (projectiveBoundaryMaps (D := D)).rlp =
      (MorphismProperty.ofHoms (representableBoundaryCell (D := D))).rlp := by
    ext X Y a
    constructor
    · intro ha U V b hb
      obtain ⟨dn, hdn⟩ := (MorphismProperty.ofHoms_iff
        (representableBoundaryCell (D := D)) b).mp hb
      have hfree : (projectiveBoundaryMaps (D := D))
          ((freeEvaluationFunctor.obj dn.1).map (SSet.boundary.{u} dn.2).ι) :=
        MorphismProperty.map_mem_adjointFamilyGenerators
          (fun e : Dᵒᵖ => freeEvaluationFunctor.obj e.unop)
          SSet.modelCategoryQuillen.I.{u} (op dn.1) (SSet.boundary.{u} dn.2).ι
          (MorphismProperty.ofHoms.mk (f := fun n : ℕ => (SSet.boundary.{u} n).ι) dn.2)
      have hcell : HasLiftingProperty (representableBoundaryCell dn) a :=
        (HasLiftingProperty.iff_of_arrow_iso_left
          (freeScalarArrowIso dn.1 (SSet.boundary.{u} dn.2).ι) a).mp (ha _ hfree)
      exact (HasLiftingProperty.iff_of_arrow_iso_left (eqToIso hdn) a).mpr hcell
    · intro ha U V b hb
      obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff
        (fun e : Dᵒᵖ => freeEvaluationFunctor.obj e.unop)
        SSet.modelCategoryQuillen.I.{u} b).mp hb
      obtain ⟨n, hn⟩ := (MorphismProperty.ofHoms_iff
        (fun n : ℕ => (SSet.boundary.{u} n).ι) q.2.1.hom).mp q.2.2
      let e : Arrow.mk b ≅ Arrow.mk (representableBoundaryCell (q.1.unop, n)) :=
        eqToIso hq ≪≫ (freeEvaluationFunctor.obj q.1.unop).mapArrow.mapIso (eqToIso hn) ≪≫
          freeScalarArrowIso q.1.unop (SSet.boundary.{u} n).ι
      exact (HasLiftingProperty.iff_of_arrow_iso_left e a).mpr
        (ha _ (MorphismProperty.ofHoms.mk
          (f := representableBoundaryCell (D := D)) (q.1.unop, n)))
  have hp : (SSet.modelCategoryQuillen.I.{u}.rlp).functorCategory Dᵒᵖ
      ((representableBoundaryFactorization (D := D)).p.app f) := by
    rw [← he]
    exact (representableBoundaryFactorization (D := D)).hp f
  exact ⟨hl, he, hp, fun e =>
    SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (hp e)⟩

/-- An original left-class arrow is a concrete retract of its same constructed left factor. -/
theorem representableBoundaryFactorization_retract
    (f : Arrow (SimplicialPresheaf.{u} D)) (hf : (projectiveBoundaryMaps (D := D)).rlp.llp f.hom) :
    ∃ r : RetractArrow f.hom ((representableBoundaryFactorization (D := D)).i.app f),
      r.i.left = 𝟙 f.left ∧ r.r.left = 𝟙 f.left ∧
        r.i.right ≫ (representableBoundaryFactorization (D := D)).p.app f = 𝟙 f.right ∧
        f.hom ≫ r.i.right = (representableBoundaryFactorization (D := D)).i.app f ∧
        r.i ≫ r.r = 𝟙 (Arrow.mk f.hom) := by
  let : HasLiftingProperty f.hom ((representableBoundaryFactorization (D := D)).p.app f) :=
      hf _ ((representableBoundaryFactorization (D := D)).hp f)
  let sq : CommSq ((representableBoundaryFactorization (D := D)).i.app f) f.hom
      ((representableBoundaryFactorization (D := D)).p.app f) (𝟙 f.right) :=
    ⟨by simp⟩
  let r : RetractArrow f.hom ((representableBoundaryFactorization (D := D)).i.app f) :=
    { i := Arrow.homMk (𝟙 _) sq.lift
      r := Arrow.homMk (𝟙 _) ((representableBoundaryFactorization (D := D)).p.app f) }
  exact ⟨r, rfl, rfl, sq.fac_right, sq.fac_left, r.retract⟩

/-- Apply the same fixed factorization to the internally constructed initial-arrow functor. -/
def representableBoundaryReplacement : SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D where
  obj X := (representableBoundaryFactorization (D := D)).Z.obj (Arrow.mk (initial.to X))
  map {X Y} a := (representableBoundaryFactorization (D := D)).Z.map
    (Arrow.homMk (𝟙 (⊥_ SimplicialPresheaf.{u} D)) a (by
      apply initialIsInitial.hom_ext))
  map_id X := by
    rw [← (representableBoundaryFactorization (D := D)).Z.map_id]
    congr 1
  map_comp a b := by
    rw [← (representableBoundaryFactorization (D := D)).Z.map_comp]
    congr 1

/-- The augmentation is the original right factor, with its whole original naturality. -/
def representableBoundaryAugmentation :
    representableBoundaryReplacement (D := D) ⟶ 𝟭 (SimplicialPresheaf.{u} D) where
  app X := (representableBoundaryFactorization (D := D)).p.app (Arrow.mk (initial.to X))
  naturality X Y a := by
    let t : Arrow.mk (initial.to X) ⟶ Arrow.mk (initial.to Y) :=
      Arrow.homMk (𝟙 (⊥_ SimplicialPresheaf.{u} D)) a (by
        apply initialIsInitial.hom_ext)
    exact (representableBoundaryFactorization (D := D)).p.naturality t

/-- The original initial-to-replacement map has the same full literal cell witness. -/
def representableBoundaryReplacementCells (X : SimplicialPresheaf.{u} D) :
    RelativeCellComplex.{u} (fun (_ : (Cardinal.aleph0.{u}).ord.ToType) =>
        representableBoundaryCell (D := D))
      (initial.to ((representableBoundaryReplacement (D := D)).obj X)) := by
  have hi : (representableBoundaryFactorization (D := D)).i.app (Arrow.mk (initial.to X)) =
      initial.to ((representableBoundaryReplacement (D := D)).obj X) :=
    initialIsInitial.hom_ext _ _
  exact hi ▸ representableBoundaryFactorizationCells (Arrow.mk (initial.to X))

/-- Initial factorization, both original naturality squares, functor laws and BASE weakness. -/
theorem representableBoundaryAugmentation_laws
    {X Y Z : SimplicialPresheaf.{u} D} (a : X ⟶ Y) (b : Y ⟶ Z) :
    let Q := representableBoundaryReplacement (D := D)
    let ε := representableBoundaryAugmentation (D := D)
    let t : Arrow.mk (initial.to X) ⟶ Arrow.mk (initial.to Y) :=
      Arrow.homMk (𝟙 (⊥_ SimplicialPresheaf.{u} D)) a (by
        apply initialIsInitial.hom_ext)
    initial.to (Q.obj X) ≫ ε.app X = initial.to X ∧
      Q.map a ≫ ε.app Y = ε.app X ≫ a ∧
      (representableBoundaryFactorization (D := D)).i.app (Arrow.mk (initial.to X)) ≫ Q.map a =
        t.left ≫ (representableBoundaryFactorization (D := D)).i.app (Arrow.mk (initial.to Y)) ∧
      (representableBoundaryFactorization (D := D)).Z.map t ≫
          (representableBoundaryFactorization (D := D)).p.app (Arrow.mk (initial.to Y)) =
        (representableBoundaryFactorization (D := D)).p.app (Arrow.mk (initial.to X)) ≫ t.right ∧
      Q.map (𝟙 X) = 𝟙 (Q.obj X) ∧ Q.map (a ≫ b) = Q.map a ≫ Q.map b ∧
      (SSet.modelCategoryQuillen.I.{u}.rlp).functorCategory Dᵒᵖ (ε.app X) ∧
      SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ (ε.app X) := by
  let Q := representableBoundaryReplacement (D := D)
  let ε := representableBoundaryAugmentation (D := D)
  let t : Arrow.mk (initial.to X) ⟶ Arrow.mk (initial.to Y) :=
    Arrow.homMk (𝟙 (⊥_ SimplicialPresheaf.{u} D)) a (by
      apply initialIsInitial.hom_ext)
  have hi : (representableBoundaryFactorization (D := D)).i.app (Arrow.mk (initial.to X)) =
      initial.to (Q.obj X) :=
    initialIsInitial.hom_ext _ _
  have hp := representableBoundaryFactorization_pointwise (Arrow.mk (initial.to X))
  refine ⟨?_, ε.naturality a,
      ((representableBoundaryFactorization (D := D)).i.naturality t).symm,
      (representableBoundaryFactorization (D := D)).p.naturality t,
    Q.map_id X, Q.map_comp a b, hp.2.2.1, hp.2.2.2⟩
  rw [← hi]
  exact (representableBoundaryFactorization (D := D)).fac_app

end SimplicialPresheaf
