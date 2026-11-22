/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalGenerators
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalTrivialMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarLeibnizHom
import MathlibExt.CategoryTheory.NatTrans.TerminalArrow

/-!
# Original local boundary cells and their same-cardinal replacement
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Cardinal Opposite
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

omit [Small.{u} I] in
/-- Every actual resolved local generator is monic and weak for the ORIGINAL presentation. -/
private theorem originalLocalGenerators_le_localTrivialMonomorphisms
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hT : ∀ j, cofibrations (SimplicialPresheaf.{u} D) (T j).hom)
    (hl : ∀ j, trivialFibrations (SimplicialPresheaf.{u} D) (r j).left)
    (hr : ∀ j, trivialFibrations (SimplicialPresheaf.{u} D) (r j).right) :
    originalLocalGenerators T ≤ localTrivialMonomorphisms S := by
  intro A B a ha
  refine ⟨originalLocalGenerators_le_monomorphisms T hT a ha, ?_⟩
  intro Z hZ
  rcases ha with hbase | hlocal
  · have hc : trivialMonomorphisms D a := by
      rw [← (data D).J_left_eq]
      exact le_llp_rlp (data D).smith.J a hbase
    have hw : weakEquivalences (SimplicialPresheaf.{u} D) a := by
      change (data D).model.categoryWithWeakEquivalences.weakEquivalences a
      rw [(data D).weakEquivalences_eq]
      exact hc.2
    exact weakEquivalences_le_originalLocalEquivalences S a hw Z hZ
  · cases hlocal with
    | mk k =>
      have hterm : (originalLocalGenerators T).rlp (terminal.from Z) :=
        (originalLocalGenerators_terminal_iff_of_resolution S T r hT hl hr Z).mpr hZ
      have hw := ((originalLocalGenerators_terminal_iff T hT Z).mp hterm).2 k.1
      let : Fibration (innerHomPre (T k.1).hom Z) := (fibration_iff _).mpr
        (rawPrecomp_fibration_of_cofibration (T k.1).hom Z (hT k.1) hZ.1)
      let : WeakEquivalence (innerHomPre (T k.1).hom Z) := (weakEquivalence_iff _).mpr hw
      let : Cofibration (SSet.boundary.{u} k.2).ι :=
        SSet.modelCategoryQuillen.cofibration_of_mono _
      have hp := SSet.ihomToPullback_mem_trivialFibrations_of_right
        (SSet.boundary.{u} k.2).ι (innerHomPre (T k.1).hom Z)
      have he := (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
        (scalarLeibnizHomIso (T k.1).hom (SSet.boundary.{u} k.2).ι Z)).mpr hp.2
      exact he

omit [Small.{u} I] in
/-- Native Galois closure retains monicity and original local weakness of ALL local cells. -/
private theorem originalLocalGenerators_left_le_localTrivialMonomorphisms
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hT : ∀ j, cofibrations (SimplicialPresheaf.{u} D) (T j).hom)
    (hl : ∀ j, trivialFibrations (SimplicialPresheaf.{u} D) (r j).left)
    (hr : ∀ j, trivialFibrations (SimplicialPresheaf.{u} D) (r j).right) :
    (originalLocalGenerators T).rlp.llp ≤ localTrivialMonomorphisms S := by
  have h := originalLocalGenerators_le_localTrivialMonomorphisms S T r hT hl hr
  rw [localTrivialMonomorphisms_eq_llp] at h ⊢
  exact antitone_llp ((le_llp_iff_le_rlp _ _).mp h)


/-- Every original source/cardinal/generator capability is retained in the constructed output. -/
def originalLocalGeneratorSystemProperties
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] : Prop :=
      ℵ₀ < κ ∧ HasCardinalLT I κ ∧ HasCardinalLT D κ ∧
        HasCardinalLT (Arrow D) κ ∧ HasCardinalLT (Arrow SimplexCategory) κ ∧
        (data D).κ < κ ∧ IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ ∧
        (∀ j, IsCofibrant (T j).left ∧ cofibrations (SimplicialPresheaf.{u} D) (T j).hom ∧
          trivialFibrations (SimplicialPresheaf.{u} D) (r j).left ∧
          trivialFibrations (SimplicialPresheaf.{u} D) (r j).right ∧
          (r j).left ≫ (S j).hom = (T j).hom ≫ (r j).right) ∧
        (∀ j, IsCardinalPresentable (S j).left κ ∧ IsCardinalPresentable (S j).right κ ∧
          IsCardinalPresentable (T j).left κ ∧ IsCardinalPresentable (T j).right κ) ∧
        originalLocalGenerators T ≤ monomorphisms (SimplicialPresheaf.{u} D) ∧
        (originalLocalGenerators T).IsSmall.{u} ∧
        (∀ j, IsCardinalPresentable (localGeneratorFamily T j).left κ ∧
          IsCardinalPresentable (localGeneratorFamily T j).right κ) ∧
        (originalLocalGenerators T).IsCardinalForSmallObjectArgument κ ∧
        (originalLocalGenerators T).HasSmallObjectArgument.{u} ∧
        Nonempty (FunctorialFactorizationData
          (originalLocalGenerators T).rlp.llp (originalLocalGenerators T).rlp) ∧
        (ofHoms (fun j => (T j).hom)).IsSmall.{u} ∧
        (ofHoms (fun j => (T j).hom)).IsCardinalForSmallObjectArgument κ ∧
        (ofHoms (fun j => (T j).hom)).HasSmallObjectArgument.{u} ∧
        Nonempty (FunctorialFactorizationData
          (ofHoms (fun j => (T j).hom)).rlp.llp (ofHoms (fun j => (T j).hom)).rlp) ∧
        (∀ Z : SimplicialPresheaf.{u} D,
          (originalLocalGenerators T).rlp (terminal.from Z) ↔
            IsFibrant Z ∧ ∀ j, SSet.realizationWeakEquivalences (innerHomPre (S j).hom Z)) ∧
        (∀ Z : SimplicialPresheaf.{u} D,
          (originalLocalGenerators T).rlp (terminal.from Z) ↔
            IsFibrant Z ∧ ∀ j,
              SSet.realizationWeakEquivalences (originalDerivedPrecomp D (S j).hom Z))

/-- Constructed data for the SAME original family, resolution, cardinal and native local cells. -/
structure OriginalLocalCellData (S : I → Arrow (SimplicialPresheaf.{u} D)) where
  /-- The resolved arrows retain the ORIGINAL index. -/
  T : I → Arrow (SimplicialPresheaf.{u} D)
  /-- Both strict original comparison maps are retained. -/
  r : ∀ j, T j ⟶ S j
  /-- The final original common cardinal. -/
  κ : Cardinal.{u}
  /-- Its original regularity witness. -/
  regular : Fact κ.IsRegular
  /-- Its OWN original ordinal bottom. -/
  orderBot : OrderBot κ.ord.ToType
  /-- ALL original/resolved endpoint and augmented-generator ranks/capabilities. -/
  properties : letI := regular; letI := orderBot
    originalLocalGeneratorSystemProperties S T r κ
  /-- Eligibility at that SAME final cardinal, for the actual native factorization. -/
  eligible : letI := regular; letI := orderBot
    (originalLocalGenerators T).IsCardinalForSmallObjectArgument κ
  /-- Every original combined generator is monic and weak for S. -/
  generatorWeak : originalLocalGenerators T ≤ localTrivialMonomorphisms S
  /-- Every original native relative cell and retract remains monic and S-weak. -/
  leftWeak : (originalLocalGenerators T).rlp.llp ≤ localTrivialMonomorphisms S

private theorem exists_originalLocalCellData (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    Nonempty (OriginalLocalCellData S) := by
  obtain ⟨T, r, κ, hReg, hBot, facts⟩ := exists_original_local_generator_system S
  let : Fact κ.IsRegular := hReg
  let : OrderBot κ.ord.ToType := hBot
  have hT (j : I) := (facts.2.2.2.2.2.2.2.1 j).2.1
  have hl (j : I) := (facts.2.2.2.2.2.2.2.1 j).2.2.1
  have hr (j : I) := (facts.2.2.2.2.2.2.2.1 j).2.2.2.1
  have hJ := facts.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨{
    T := T
    r := r
    κ := κ
    regular := hReg
    orderBot := hBot
    properties := facts
    eligible := hJ
    generatorWeak := originalLocalGenerators_le_localTrivialMonomorphisms S T r hT hl hr
    leftWeak := originalLocalGenerators_left_le_localTrivialMonomorphisms S T r hT hl hr
  }⟩

/-- One actual constructed choice on S, retaining its original family and final cardinal ONCE. -/
def originalLocalCellData (S : I → Arrow (SimplicialPresheaf.{u} D)) : OriginalLocalCellData S :=
  Classical.choice (exists_originalLocalCellData S)

/-- The literal SAME-cardinal native functorial factorization, not an arbitrary factorization
choice. -/
def originalLocalCellFactorization (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    FunctorialFactorizationData (originalLocalGenerators (originalLocalCellData S).T).rlp.llp
      (originalLocalGenerators (originalLocalCellData S).T).rlp := by
  let d := originalLocalCellData S
  letI := d.regular
  letI := d.orderBot
  letI := d.eligible
  exact SmallObject.functorialFactorizationData (originalLocalGenerators d.T) d.κ

/-- The actual original object replacement is the native factorization of its terminal arrow. -/
def originalLocalCellReplacement (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D :=
  terminal.arrowFunctor (SimplicialPresheaf.{u} D) ⋙ (originalLocalCellFactorization S).Z

/-- The original natural weak-unit components are literally the native factorization i. -/
def originalLocalCellUnit (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    𝟭 (SimplicialPresheaf.{u} D) ⟶ originalLocalCellReplacement S where
  app X := (originalLocalCellFactorization S).i.app
    ((terminal.arrowFunctor (SimplicialPresheaf.{u} D)).obj X)
  naturality X Y f := by
    simpa [originalLocalCellReplacement] using (originalLocalCellFactorization S).i.naturality
      ((terminal.arrowFunctor (SimplicialPresheaf.{u} D)).map f)

/-- The original natural terminal projection is literally the native factorization p. -/
def originalLocalCellProjection (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    originalLocalCellReplacement S ⟶ (Functor.const (SimplicialPresheaf.{u} D)).obj
      (⊤_ SimplicialPresheaf.{u} D) where
  app X := (originalLocalCellFactorization S).p.app
    ((terminal.arrowFunctor (SimplicialPresheaf.{u} D)).obj X)
  naturality X Y f := by
    simpa [originalLocalCellReplacement] using (originalLocalCellFactorization S).p.naturality
      ((terminal.arrowFunctor (SimplicialPresheaf.{u} D)).map f)


/-- The entire original terminal-arrow factorization equation. -/
@[reassoc]
theorem originalLocalCellUnit_projection (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    (originalLocalCellUnit S).app X ≫ (originalLocalCellProjection S).app X = terminal.from X :=
  (originalLocalCellFactorization S).fac_app

/-- Every original unit is in the SAME native left factor class. -/
theorem originalLocalCellUnit_mem_left (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    (originalLocalGenerators (originalLocalCellData S).T).rlp.llp
      ((originalLocalCellUnit S).app X) :=
  (originalLocalCellFactorization S).hi (Arrow.mk (terminal.from X))

/-- Every original terminal projection is in the SAME actual generator RLP class. -/
theorem originalLocalCellProjection_mem_right (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    (originalLocalGenerators (originalLocalCellData S).T).rlp
      ((originalLocalCellProjection S).app X) :=
  (originalLocalCellFactorization S).hp (Arrow.mk (terminal.from X))

/-- The constructed unit is monic and weak for the ORIGINAL S, without a base-weak claim. -/
theorem originalLocalCellUnit_mono_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    Mono ((originalLocalCellUnit S).app X) ∧
      originalLocalEquivalences S ((originalLocalCellUnit S).app X) :=
  (originalLocalCellData S).leftWeak _ (originalLocalCellUnit_mem_left S X)

/-- The SAME terminal criterion gives GLOBAL original injective fibrancy and S-locality. -/
theorem originalLocalCellReplacement_localFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (X : SimplicialPresheaf.{u} D) :
    isOriginalLocalFibrant S ((originalLocalCellReplacement S).obj X) := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  rcases d.properties with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRaw, _⟩
  have hp : (originalLocalGenerators d.T).rlp
      (terminal.from ((originalLocalCellReplacement S).obj X)) := by
    have he : (originalLocalCellProjection S).app X =
        terminal.from ((originalLocalCellReplacement S).obj X) :=
      terminalIsTerminal.hom_ext _ _
    rw [← he]
    exact originalLocalCellProjection_mem_right S X
  exact (hRaw _).mp hp

/-- The unit naturality retains EVERY original map, not only weak or monic maps. -/
@[reassoc]
theorem originalLocalCellUnit_naturality (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    (originalLocalCellUnit S).app X ≫ (originalLocalCellReplacement S).map f =
      f ≫ (originalLocalCellUnit S).app Y :=
  ((originalLocalCellUnit S).naturality f).symm

/-- Both original terminal projection maps survive the arbitrary source map. -/
@[reassoc]
theorem originalLocalCellProjection_naturality (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    (originalLocalCellReplacement S).map f ≫ (originalLocalCellProjection S).app Y =
      (originalLocalCellProjection S).app X := by
  exact terminalIsTerminal.hom_ext _ _

/-- The SAME unit is the literal native relative cell complex on the returned ordinal. -/
def originalLocalCellUnitComplex (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    RelativeCellComplex.{u} (fun (_ : d.κ.ord.ToType) => (originalLocalGenerators d.T).homFamily)
      ((originalLocalCellUnit S).app X) := by
  let d := originalLocalCellData S
  letI := d.regular
  letI := d.orderBot
  letI := d.eligible
  exact SmallObject.relativeCellComplexιObj (originalLocalGenerators d.T) d.κ (terminal.from X)


/-- The unit component is exactly the original native terminal-arrow inclusion. -/
theorem originalLocalCellUnit_app (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    (originalLocalCellUnit S).app X =
      (originalLocalCellFactorization S).i.app (Arrow.mk (terminal.from X)) := rfl

/-- The projection component is exactly the original native terminal-arrow projection. -/
theorem originalLocalCellProjection_app (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) :
    (originalLocalCellProjection S).app X =
      (originalLocalCellFactorization S).p.app (Arrow.mk (terminal.from X)) := rfl

/-- The SAME native factorization retains its returned regularity, bottom and cardinal
eligibility. -/
theorem originalLocalCellFactorization_eq (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    originalLocalCellFactorization S =
      SmallObject.functorialFactorizationData (originalLocalGenerators d.T) d.κ := rfl

/-- Original derived locality follows for the actual constructed target of the SAME unit. -/
theorem originalLocalCellReplacement_derivedLocalFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (X : SimplicialPresheaf.{u} D) :
    IsFibrant ((originalLocalCellReplacement S).obj X) ∧
      ∀ j, SSet.realizationWeakEquivalences
        (originalDerivedPrecomp D (S j).hom ((originalLocalCellReplacement S).obj X)) := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  rcases d.properties with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hDerived⟩
  have he : (originalLocalCellProjection S).app X =
      terminal.from ((originalLocalCellReplacement S).obj X) := terminalIsTerminal.hom_ext _ _
  apply (hDerived _).mp
  rw [← he]
  exact originalLocalCellProjection_mem_right S X

/-- The exact native successor point is retained in the original unit's cell witness. -/
def originalLocalCellUnitSuccIso (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : SimplicialPresheaf.{u} D) (j : (originalLocalCellData S).κ.ord.ToType) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    letI := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
    letI := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
    (originalLocalCellUnitComplex S X).F.obj (Order.succ j) ≅
      SmallObject.functorObj (originalLocalGenerators d.T).homFamily
        (((SmallObject.iterationFunctor (originalLocalGenerators d.T) d.κ).obj j).obj
          (Arrow.mk (terminal.from X))).hom := by
  let d := originalLocalCellData S
  letI := d.regular
  letI := d.orderBot
  letI := d.eligible
  exact SmallObject.relativeCellComplexιObjFObjSuccIso
    (originalLocalGenerators d.T) d.κ (terminal.from X) j

/-- The actual original successor inclusion equation uses the SAME cell objects and ordinal. -/
theorem originalLocalCellUnit_successor_inclusion
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (X : SimplicialPresheaf.{u} D)
    (j : (originalLocalCellData S).κ.ord.ToType) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    letI := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
    letI := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
    SmallObject.ιFunctorObj (originalLocalGenerators d.T).homFamily
      (((SmallObject.iterationFunctor (originalLocalGenerators d.T) d.κ).obj j).obj
        (Arrow.mk (terminal.from X))).hom =
      (originalLocalCellUnitComplex S X).F.map (homOfLE (Order.le_succ j)) ≫
        (originalLocalCellUnitSuccIso S X j).hom := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  exact SmallObject.ιFunctorObj_eq (originalLocalGenerators d.T) d.κ (terminal.from X) j

/-- The actual original successor projection retains the SAME final projection and original
target. -/
theorem originalLocalCellUnit_successor_projection
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (X : SimplicialPresheaf.{u} D)
    (j : (originalLocalCellData S).κ.ord.ToType) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    letI := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
    letI := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
    SmallObject.πFunctorObj (originalLocalGenerators d.T).homFamily
      (((SmallObject.iterationFunctor (originalLocalGenerators d.T) d.κ).obj j).obj
        (Arrow.mk (terminal.from X))).hom =
      (originalLocalCellUnitSuccIso S X j).inv ≫
        (originalLocalCellUnitComplex S X).incl.app (Order.succ j) ≫
        (originalLocalCellProjection S).app X ≫
        (SmallObject.iterationFunctorObjObjRightIso (originalLocalGenerators d.T) d.κ
          (Arrow.mk (terminal.from X)) j).inv := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  exact SmallObject.πFunctorObj_eq (originalLocalGenerators d.T) d.κ (terminal.from X) j

/-- The whole original local cell system, natural weak unit and globally local target are
constructed. -/
theorem exists_original_local_cell_unit_system
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    ∃ d : OriginalLocalCellData S, d = originalLocalCellData S ∧
      (∀ X : SimplicialPresheaf.{u} D,
        (originalLocalCellUnit S).app X ≫ (originalLocalCellProjection S).app X = terminal.from X ∧
        (originalLocalGenerators d.T).rlp.llp ((originalLocalCellUnit S).app X) ∧
        (originalLocalGenerators d.T).rlp ((originalLocalCellProjection S).app X) ∧
        Mono ((originalLocalCellUnit S).app X) ∧
        originalLocalEquivalences S ((originalLocalCellUnit S).app X) ∧
        isOriginalLocalFibrant S ((originalLocalCellReplacement S).obj X)) := by
  refine ⟨originalLocalCellData S, rfl, fun X => ?_⟩
  exact ⟨originalLocalCellUnit_projection S X, originalLocalCellUnit_mem_left S X,
    originalLocalCellProjection_mem_right S X, (originalLocalCellUnit_mono_weak S X).1,
    (originalLocalCellUnit_mono_weak S X).2, originalLocalCellReplacement_localFibrant S X⟩

end SimplicialPresheaf.InjectiveKan
