/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.SpineSaturation
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Segal row restrictions and right powers

A vertically Reedy-fibrant simplicial space satisfying the original Segal
spine-locality maps has trivial unary left restrictions along inner anodyne
maps, inner right restrictions along monomorphisms, and quasi-category right
powers. These are the forward clauses of Joyal–Tierney Proposition 3.4.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

universe u

namespace SimplicialSpace

private abbrev leftRestriction (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    (SimplicialSpace.boxLeftDivisionFunctor.obj (op B)).obj X ⟶
      (SimplicialSpace.boxLeftDivisionFunctor.obj (op A)).obj X :=
  (SimplicialSpace.boxLeftDivisionFunctor.map a.op).app X

private def PX (X : SimplicialSpace.{u}) : MorphismProperty SSet.{u} :=
  monomorphisms SSet.{u} ⊓
    (MorphismProperty.ofHoms (fun m : ℕ => SimplicialSpace.rowMatchingMap m X)).llp

private instance (X : SimplicialSpace.{u}) : (PX X).IsMultiplicative := by
  dsimp only [PX]
  infer_instance

private instance (X : SimplicialSpace.{u}) : (PX X).RespectsIso := by
  dsimp only [PX]
  infer_instance

private instance (X : SimplicialSpace.{u}) : (PX X).IsStableUnderCobaseChange := by
  dsimp only [PX]
  infer_instance

private instance (X : SimplicialSpace.{u}) : (PX X).IsStableUnderTransfiniteComposition.{u} := by
  constructor
  intro J _ _ _ _
  dsimp only [PX]
  have _ : (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape J :=
    inferInstance
  have _ : (MorphismProperty.ofHoms
      (fun m : ℕ => SimplicialSpace.rowMatchingMap m
          X)).llp.IsStableUnderTransfiniteCompositionOfShape J :=
    inferInstance
  constructor
  intro A B a ha
  obtain ⟨ha⟩ := ha
  exact ⟨transfiniteCompositionsOfShape_le (monomorphisms SSet.{u}) J _
      ⟨ha.ofLE inf_le_left⟩,
    transfiniteCompositionsOfShape_le
      (MorphismProperty.ofHoms (fun m : ℕ => SimplicialSpace.rowMatchingMap m X)).llp J _
      ⟨ha.ofLE inf_le_right⟩⟩

private instance (X : SimplicialSpace.{u}) : (PX X).IsStableUnderRetracts := by
  dsimp only [PX]
  infer_instance

private def underArrow (Z : SSet.{u}) : Under Z ⥤ Arrow SSet.{u} where
  obj A := Arrow.mk A.hom
  map f := Arrow.homMk (𝟙 Z) f.right (by simp)
  map_id A := by
    apply Arrow.hom_ext
    · simp
    · rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · simp
    · rfl

private lemma PX_codomain_retract (X : SimplicialSpace.{u}) (Z : SSet.{u})
    (A B : Under Z) (h : Retract A B) (hB : PX X B.hom) : PX X A.hom :=
  MorphismProperty.of_retract (h.map (underArrow Z)) hB

private lemma PX_mono (X : SimplicialSpace.{u}) : PX X ≤ monomorphisms SSet.{u} :=
  inf_le_left

private abbrev leftTerminalSquare (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (terminal.from X) := by
  let _ : (SimplicialSpace.boxLeftDivisionFunctor.obj (op A)).IsRightAdjoint :=
    (SimplicialSpace.boxProductLeftAdjunction₂.adj A).isRightAdjoint
  let _ : (SimplicialSpace.boxLeftDivisionFunctor.obj (op B)).IsRightAdjoint :=
    (SimplicialSpace.boxProductLeftAdjunction₂.adj B).isRightAdjoint
  exact Functor.PullbackObjObj.ofIsTerminal SimplicialSpace.boxLeftDivisionFunctor
    a (terminal.from X) terminalIsTerminal

private def leftTerminalPointIso (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).pt ≅
      (SimplicialSpace.boxLeftDivisionFunctor.obj (op A)).obj X :=
  (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).isPullback.isoIsPullback
    _ _ (leftTerminalSquare X a).isPullback

private lemma leftTerminalPointIso_hom_fst (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    (leftTerminalPointIso X a).hom ≫ (leftTerminalSquare X a).fst =
      (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).fst :=
  IsPullback.isoIsPullback_hom_fst _ _
    (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).isPullback
    (leftTerminalSquare X a).isPullback

private lemma leftTerminalPointIso_hom_snd (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    (leftTerminalPointIso X a).hom ≫ (leftTerminalSquare X a).snd =
      (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).snd :=
  IsPullback.isoIsPullback_hom_snd _ _
    (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).isPullback
    (leftTerminalSquare X a).isPullback

set_option backward.isDefEq.respectTransparency false in
private def leftTerminalArrowIso (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    Arrow.mk (SimplicialSpace.boxLeftPullbackHom a (terminal.from X)) ≅
      Arrow.mk (leftRestriction X a) :=
  Arrow.isoMk (Iso.refl _) (leftTerminalPointIso X a) (by
    change (leftTerminalSquare X a).π =
      (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).π ≫
        (leftTerminalPointIso X a).hom
    symm
    apply (leftTerminalSquare X a).isPullback.hom_ext
    · rw [Category.assoc, leftTerminalPointIso_hom_fst,
        (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).π_fst,
        (leftTerminalSquare X a).π_fst]
    · rw [Category.assoc, leftTerminalPointIso_hom_snd,
        (SimplicialSpace.boxLeftPullbackHomSquare a (terminal.from X)).π_snd,
        (leftTerminalSquare X a).π_snd])

private lemma PX_iff_left_boundaryRLP (X : SimplicialSpace.{u})
    {A B : SSet.{u}} (a : A ⟶ B) :
    PX X a ↔ Mono a ∧ SSet.modelCategoryQuillen.I.rlp (leftRestriction X a) := by
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro C D i hi
    change MorphismProperty.ofHoms (fun m : ℕ => (SSet.boundary.{u} m).ι) i at hi
    cases hi with
    | mk m =>
      have hr : HasLiftingProperty a (SimplicialSpace.rowMatchingMap m X) :=
        h _ (MorphismProperty.ofHoms.mk m)
      have hp : HasLiftingProperty a
          (SimplicialSpace.rowPullbackHom (SSet.boundary.{u} m).ι (terminal.from X)) :=
        (HasLiftingProperty.iff_of_arrow_iso_right a
          (SimplicialSpace.rowPullbackHomTerminalArrowIso (SSet.boundary.{u} m).ι X)).mpr hr
      have hl := (SimplicialSpace.box_hasLiftingProperty_iff
        a (SSet.boundary.{u} m).ι (terminal.from X)).mp hp
      exact (HasLiftingProperty.iff_of_arrow_iso_right (SSet.boundary.{u} m).ι
        (leftTerminalArrowIso X a)).mp hl
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro C D i hi
    cases hi with
    | mk m =>
      have hl : HasLiftingProperty (SSet.boundary.{u} m).ι
          (SimplicialSpace.boxLeftPullbackHom a (terminal.from X)) :=
        (HasLiftingProperty.iff_of_arrow_iso_right (SSet.boundary.{u} m).ι
          (leftTerminalArrowIso X a)).mpr
            (h _ (SSet.modelCategoryQuillen.boundary_ι_mem_I m))
      have hp := (SimplicialSpace.box_hasLiftingProperty_iff
        a (SSet.boundary.{u} m).ι (terminal.from X)).mpr hl
      exact (HasLiftingProperty.iff_of_arrow_iso_right a
        (SimplicialSpace.rowPullbackHomTerminalArrowIso (SSet.boundary.{u} m).ι X)).mp hp

private lemma mono_discrete {A B : SSet.{u}} (a : A ⟶ B) [Mono a] :
    Mono (SimplicialSpace.discreteInnerMap a) := by
  let _ : (SimplicialObject.const (Type u)).PreservesMonomorphisms := inferInstance
  let _ : Mono (SSet.simplicialSpaceDiscrete.map a) := by
    change Mono (((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) SSet.{u}).obj
      (SimplicialObject.const (Type u))).map a)
    infer_instance
  exact inferInstanceAs (Mono (SimplicialSpace.ofSimplicialObject.map
    (SSet.simplicialSpaceDiscrete.map a)))

private lemma leftRestriction_kanFibration (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X) {A B : SSet.{u}} (a : A ⟶ B) [Mono a] :
    SSet.modelCategoryQuillen.J.rlp (leftRestriction X a) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hcof : cofibrations SimplicialSpace.{u} (SimplicialSpace.discreteInnerMap a) :=
    (HomotopicalAlgebra.cofibration_iff _).mp
      ((SimplicialSpace.ReedyModel.cofibration_iff _).mpr (mono_discrete a))
  exact SimplicialSpace.ReedyModel.inner_precomp_fibration
    (SimplicialSpace.discreteInnerMap a) X hcof hX

private lemma leftRestriction_comp (X : SimplicialSpace.{u})
    {A B C : SSet.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    leftRestriction X b ≫ leftRestriction X a = leftRestriction X (a ≫ b) := by
  dsimp only [leftRestriction]
  rw [← NatTrans.comp_app, ← SimplicialSpace.boxLeftDivisionFunctor.map_comp, ← op_comp]

private lemma realizationWeak_of_boundaryRLP {A B : SSet.{u}} (p : A ⟶ B)
    (hp : SSet.modelCategoryQuillen.I.rlp p) : SSet.realizationWeakEquivalences p := by
  have hm : (monomorphisms SSet.{u}).rlp p := by
    rw [SSet.rlp_monomorphisms]
    exact hp
  let _ : Fibration p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mpr
      ((antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms) _ hm)
  exact (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mp hp

private lemma PX_cancel (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X) {A B C : SSet.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (ha : Mono a) (hb : Mono b) (hPa : PX X a) (hPab : PX X (a ≫ b)) : PX X b := by
  let _ : Mono a := ha
  let _ : Mono b := hb
  have haI := ((PX_iff_left_boundaryRLP X a).mp hPa).2
  have habI := ((PX_iff_left_boundaryRLP X (a ≫ b)).mp hPab).2
  have haW := realizationWeak_of_boundaryRLP _ haI
  have habW := realizationWeak_of_boundaryRLP _ habI
  have hbW : SSet.realizationWeakEquivalences (leftRestriction X b) := by
    apply SSet.realizationWeakEquivalences.of_postcomp _ _ haW
    rw [leftRestriction_comp]
    exact habW
  let _ : Fibration (leftRestriction X b) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr (leftRestriction_kanFibration X hX b)
  exact (PX_iff_left_boundaryRLP X b).mpr ⟨hb,
    (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mpr hbW⟩

private lemma innerAnodyne_le_PX (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X)
    (hSpine : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      (leftRestriction X (SSet.Rezk.spineSubcomplex.{u} n).ι)) :
    SSet.innerAnodyneExtensions ≤ PX X := by
  apply SSet.innerAnodyneExtensions_le_of_spines (PX X) (PX_mono X)
    (PX_codomain_retract X) (PX_cancel X hX)
  intro n hn
  let _ : Fibration (leftRestriction X (SSet.Rezk.spineSubcomplex.{u} n).ι) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr
      (leftRestriction_kanFibration X hX _)
  exact (PX_iff_left_boundaryRLP X _).mpr ⟨inferInstance,
    (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mpr
      (hSpine n hn)⟩

private lemma rowRestriction_inner_of_PX (X : SimplicialSpace.{u})
    (hPX : SSet.innerAnodyneExtensions ≤ PX X)
    {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.InnerFibration (SimplicialSpace.rowRestriction v X) := by
  constructor
  intro A B a ha
  have hinner : SSet.innerAnodyneExtensions a := le_llp_rlp _ _ ha
  have hI := ((PX_iff_left_boundaryRLP X a).mp (hPX _ hinner)).2
  have hm : (monomorphisms SSet.{u}).rlp (leftRestriction X a) := by
    rw [SSet.rlp_monomorphisms]
    exact hI
  have hl : HasLiftingProperty v
      (SimplicialSpace.boxLeftPullbackHom a (terminal.from X)) :=
    (HasLiftingProperty.iff_of_arrow_iso_right v (leftTerminalArrowIso X a)).mpr
      (hm v inferInstance)
  have hp := (SimplicialSpace.box_hasLiftingProperty_iff a v (terminal.from X)).mpr hl
  exact (HasLiftingProperty.iff_of_arrow_iso_right a
    (SimplicialSpace.rowPullbackHomTerminalArrowIso v X)).mp hp

private def empty_row_power_isTerminal (X : SimplicialSpace.{u}) :
    IsTerminal ((SimplicialSpace.rowPowerFunctor (⊥_ SSet.{u})).obj X) := by
  let _ : ∀ A : SSet.{u}, PreservesColimitsOfShape (Discrete PEmpty.{1})ᵒᵖ
      (SimplicialSpace.boxProduct.flip.flip.obj A) := fun A => by
    change PreservesColimitsOfShape (Discrete PEmpty.{1})ᵒᵖ
      (SimplicialSpace.boxProduct.obj A)
    let _ : (SimplicialSpace.boxProduct.obj A).IsLeftAdjoint :=
      (SimplicialSpace.boxProductLeftAdjunction₂.adj A).isLeftAdjoint
    infer_instance
  let _ : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SimplicialSpace.rowPowerBifunctor.flip.obj X) :=
    SimplicialSpace.boxProductRightAdjunction₂.preservesLimitsOfShape_flip_obj
      (Discrete PEmpty.{1}) X
  exact (initialIsInitial.op : IsTerminal (op (⊥_ SSet.{u}))).isTerminalObj
    (SimplicialSpace.rowPowerBifunctor.flip.obj X) _

private lemma rowPower_quasi_of_PX (X : SimplicialSpace.{u})
    (hPX : SSet.innerAnodyneExtensions ≤ PX X) (S : SSet.{u}) :
    SSet.Quasicategory ((SimplicialSpace.rowPowerFunctor S).obj X) := by
  let _ : Mono (initial.to S) := inferInstance
  exact (SSet.quasicategory_iff_of_isTerminal
    (SimplicialSpace.rowRestriction (initial.to S) X) (empty_row_power_isTerminal X)).mpr
      (rowRestriction_inner_of_PX X hPX (initial.to S))

/-- Every original unary left restriction along an inner anodyne map has boundary RLP. -/
theorem leftRestriction_boundaryRLP_of_innerAnodyne (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X)
    (hSpine : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((SimplicialSpace.boxLeftDivisionFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app X))
    {A B : SSet.{u}} (a : A ⟶ B) (ha : SSet.innerAnodyneExtensions a) :
    SSet.modelCategoryQuillen.I.rlp ((SimplicialSpace.boxLeftDivisionFunctor.map a.op).app X) :=
  ((PX_iff_left_boundaryRLP X a).mp ((innerAnodyne_le_PX X hX hSpine) _ ha)).2

/-- The original monic right restrictions are inner from the exact Segal input maps. -/
theorem rowRestriction_inner_of_spines (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X)
    (hSpine : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((SimplicialSpace.boxLeftDivisionFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app X))
    {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.InnerFibration (SimplicialSpace.rowRestriction v X) :=
  rowRestriction_inner_of_PX X (innerAnodyne_le_PX X hX hSpine) v

/-- Every original right power is quasi; no row or power fibrancy premise is added. -/
theorem rowPower_quasi_of_spines (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X)
    (hSpine : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((SimplicialSpace.boxLeftDivisionFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app X))
    (S : SSet.{u}) : SSet.Quasicategory ((SimplicialSpace.rowPowerFunctor S).obj X) :=
  rowPower_quasi_of_PX X (innerAnodyne_le_PX X hX hSpine) S

end SimplicialSpace
