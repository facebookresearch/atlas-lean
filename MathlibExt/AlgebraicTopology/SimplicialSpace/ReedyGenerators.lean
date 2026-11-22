/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RelativeBoundaryMatching
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerationCardinal
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyModel
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Literal lifting classes and generation of the named Reedy model
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SimplicialSpace.Inner
namespace SimplicialSpace.ReedyGeneratingFamilies


private lemma boundary_lifting_iff (m n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    HasLiftingProperty (boundaryPushout.{u} m n).ι p ↔
      HasLiftingProperty (SSet.boundary.{u} n).ι
        (SimplicialObject.relativeMatchingMap (forget.map p) m) := by
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u} (outerBoundaryMap.{u} m) p
  let e : Arrow.mk q.π ≅
      Arrow.mk (SimplicialObject.relativeMatchingMap (forget.map p) m) :=
    (relativeBoundaryMatchingArrowIso.{u} m).app (Arrow.mk p)
  exact (innerTensorHomAdjunction₂.{u}.hasLiftingProperty_iff
    (boundaryPushout.{u} m n) q).trans
      (HasLiftingProperty.iff_of_arrow_iso_right (SSet.boundary.{u} n).ι e)

private lemma horn_lifting_iff (m : ℕ) (n : {n : ℕ // 1 ≤ n})
    (i : Fin (n.1 + 1)) {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    HasLiftingProperty (hornPushout.{u} m n i).ι p ↔
      HasLiftingProperty (SSet.horn.{u} n.1 i).ι
        (SimplicialObject.relativeMatchingMap (forget.map p) m) := by
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u} (outerBoundaryMap.{u} m) p
  let e : Arrow.mk q.π ≅
      Arrow.mk (SimplicialObject.relativeMatchingMap (forget.map p) m) :=
    (relativeBoundaryMatchingArrowIso.{u} m).app (Arrow.mk p)
  exact (innerTensorHomAdjunction₂.{u}.hasLiftingProperty_iff
    (hornPushout.{u} m n i) q).trans
      (HasLiftingProperty.iff_of_arrow_iso_right (SSet.horn.{u} n.1 i).ι e)


private lemma I_rlp_matching_iff {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    I.{u}.rlp p ↔ ∀ m : ℕ, SSet.modelCategoryQuillen.I.{u}.rlp
      (SimplicialObject.relativeMatchingMap (forget.map p) m) := by
  constructor
  · intro hp m A B i hi
    change MorphismProperty.ofHoms (fun n : ℕ => (SSet.boundary.{u} n).ι) i at hi
    cases hi with
    | mk n =>
      exact (boundary_lifting_iff m n p).mp
        (hp (boundaryFamily.{u} (m, n)).hom (MorphismProperty.ofHoms.mk (m, n)))
  · intro hm A B i hi
    change MorphismProperty.ofHoms
      (fun b : BoundaryIndex => (boundaryFamily.{u} b).hom) i at hi
    cases hi with
    | mk b =>
      exact (boundary_lifting_iff b.1 b.2 p).mpr
        (hm b.1 _ (SSet.modelCategoryQuillen.boundary_ι_mem_I b.2))

private lemma J_rlp_matching_iff {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    J.{u}.rlp p ↔ ∀ m : ℕ, SSet.modelCategoryQuillen.J.{u}.rlp
      (SimplicialObject.relativeMatchingMap (forget.map p) m) := by
  constructor
  · intro hp m A B i hi
    change (⨆ k : ℕ, MorphismProperty.ofHoms
      (fun face : Fin (k + 2) => (SSet.horn.{u} (k + 1) face).ι)) i at hi
    rcases (MorphismProperty.iSup_iff _ _).mp hi with ⟨k, hi⟩
    cases hi with
    | mk face =>
      let n : {n : ℕ // 1 ≤ n} := ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
      have hmem : J.{u} (hornFamily.{u} (m, ⟨n, face⟩)).hom :=
        MorphismProperty.ofHoms.mk
          (f := fun h : HornIndex => (hornFamily.{u} h).hom) (m, ⟨n, face⟩)
      have hl : HasLiftingProperty (hornPushout.{u} m n face).ι p := hp _ hmem
      exact (horn_lifting_iff m n face p).mp hl
  · intro hm A B i hi
    change MorphismProperty.ofHoms
      (fun h : HornIndex => (hornFamily.{u} h).hom) i at hi
    cases hi with
    | mk h =>
      let n := h.2.1
      let _ : NeZero n.1 := ⟨by
        intro hn
        have hnpos := n.2
        rw [hn] at hnpos
        exact Nat.not_succ_le_zero 0 hnpos⟩
      exact (horn_lifting_iff h.1 n h.2.2 p).mpr
        (hm h.1 _ (SSet.modelCategoryQuillen.horn_ι_mem_J n.1 h.2.2))

private lemma I_rlp_eq_matching :
    I.{u}.rlp =
      (SimplicialObject.reedyRight SSet.modelCategoryQuillen.I.{u}.rlp).inverseImage forget := by
  apply MorphismProperty.ext
  intro X Y p
  exact I_rlp_matching_iff p

private lemma J_rlp_eq_matching :
    J.{u}.rlp =
      (SimplicialObject.reedyRight SSet.modelCategoryQuillen.J.{u}.rlp).inverseImage forget := by
  apply MorphismProperty.ext
  intro X Y p
  exact J_rlp_matching_iff p

private lemma scalar_I_rlp_eq_true_trivialFibrations :
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    SSet.modelCategoryQuillen.I.{u}.rlp = trivialFibrations SSet.{u} := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  rw [← SSet.rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp = trivialFibrations SSet.{u}
  exact cofibrations_rlp SSet.{u}

theorem J_rlp_eq_fibrations :
    let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    J.{u}.rlp = fibrations SimplicialSpace.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  apply MorphismProperty.ext
  intro X Y p
  exact (J_rlp_matching_iff p).trans
    ((ReedyModel.fibration_iff p).symm.trans (HomotopicalAlgebra.fibration_iff p))

theorem I_rlp_eq_trivialFibrations :
    let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    I.{u}.rlp = trivialFibrations SimplicialSpace.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  calc
    I.{u}.rlp = (SimplicialObject.reedyRight
        SSet.modelCategoryQuillen.I.{u}.rlp).inverseImage forget := I_rlp_eq_matching
    _ = (SimplicialObject.reedyRight
        (trivialFibrations SSet.{u})).inverseImage forget := by
      rw [scalar_I_rlp_eq_true_trivialFibrations]
    _ = (SimplicialObject.reedyRight (fibrations SSet.{u}) ⊓
        (weakEquivalences SSet.{u}).functorCategory SimplexCategoryᵒᵖ).inverseImage forget := by
      rw [SimplicialObject.reedyRight_trivialFibrations_eq]
    _ = trivialFibrations SimplicialSpace.{u} := by
      -- Remaining definitional normalization of the actual named transported
      -- parent roles; no pointwise-TF=Reedy-TF assertion or supplied equality.
      rw [MorphismProperty.inverseImage_inf]
      rfl

/-- The literal families generate the named Reedy model at one common cardinal. -/
theorem exists_cofibrantGenerationData :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      IsCardinalLocallyPresentable SimplicialSpace.{u} κ ∧
        ∃ (hI : I.{u}.IsCardinalForSmallObjectArgument κ)
          (hJ : J.{u}.IsCardinalForSmallObjectArgument κ),
          letI : I.{u}.IsCardinalForSmallObjectArgument κ := hI
          letI : J.{u}.IsCardinalForSmallObjectArgument κ := hJ
          ∃ (cg : CofibrantGenerationData SimplicialSpace.{u} κ),
            cg.I = I.{u} ∧ cg.J = J.{u} ∧
              ∃ (dI : FunctorialFactorizationData I.{u}.rlp.llp I.{u}.rlp)
                (dJ : FunctorialFactorizationData J.{u}.rlp.llp J.{u}.rlp),
                dI = SmallObject.functorialFactorizationData I.{u} κ ∧
                dJ = SmallObject.functorialFactorizationData J.{u} κ := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  obtain ⟨κ, hκ, hbot, h⟩ := exists_generation_cardinal.{u}
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  rcases h with ⟨hC, hI, hJ, dI, dJ, hdI, hdJ⟩
  let _ : I.{u}.IsCardinalForSmallObjectArgument κ := hI
  let _ : J.{u}.IsCardinalForSmallObjectArgument κ := hJ
  let cg : CofibrantGenerationData SimplicialSpace.{u} κ :=
    { I := I.{u}
      J := J.{u}
      I_smallObject := hI
      J_smallObject := hJ
      I_rlp := I_rlp_eq_trivialFibrations.{u}
      J_rlp := J_rlp_eq_fibrations.{u} }
  exact ⟨κ, hκ, hbot, hC, hI, hJ, cg, rfl, rfl, dI, dJ, hdI, hdJ⟩

end SimplicialSpace.ReedyGeneratingFamilies
