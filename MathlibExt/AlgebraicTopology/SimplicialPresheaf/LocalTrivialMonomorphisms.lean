/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalTests
import MathlibExt.CategoryTheory.LiftingProperties.LeibnizMate
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Original local trivial monomorphisms as a lifting class

The actual scalar tensor/cotensor mates give original boundary right tests.
Together with the actual base trivial fibrations, their left lifting class
is exactly the original monic local weak class. No local model or closure
packet is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The original scalar boundary transformation between actual fixed tensor functors. -/
def boundaryTensorTransformation (n : ℕ) :
    scalarTensorFixed (D := D) ((SSet.boundary.{u} n) : SSet.{u}) ⟶
      scalarTensorFixed (D := D) (Δ[n] : SSet.{u}) where
  app A := (scalarTensor.obj A).map (SSet.boundary.{u} n).ι
  naturality A B f := by
    change (scalarTensor.map f).app _ ≫ (scalarTensor.obj B).map _ =
      (scalarTensor.obj A).map _ ≫ (scalarTensor.map f).app _
    exact ((scalarTensor.map f).naturality (SSet.boundary.{u} n).ι).symm

/-- The genuine conjugate mate of the original boundary tensor transformation. -/
def boundaryCotensorMate (n : ℕ) :
    (scalarCotensor (D := D)).obj (op (Δ[n] : SSet.{u})) ⟶
      (scalarCotensor (D := D)).obj (op ((SSet.boundary.{u} n) : SSet.{u})) :=
  conjugateEquiv (scalarTensorCotensorAdjunction (D := D) (Δ[n] : SSet.{u}))
    (scalarTensorCotensorAdjunction (D := D) ((SSet.boundary.{u} n) : SSet.{u}))
    (boundaryTensorTransformation (D := D) n)

/-- The actual cotensor pullback corner at the original terminal map. -/
def localBoundaryCotensorCorner (n : ℕ) (Z : SimplicialPresheaf.{u} D) :
    (walkingParallelPairOp.leftOp ⋙
      parallelPair (boundaryCotensorMate (D := D) n)
          (boundaryCotensorMate (D := D) n)).PullbackObjObj WalkingParallelPairHom.left
          (terminal.from Z) :=
  Functor.PullbackObjObj.ofHasPullback
    (walkingParallelPairOp.leftOp ⋙ parallelPair
      (boundaryCotensorMate (D := D) n) (boundaryCotensorMate (D := D) n))
    WalkingParallelPairHom.left (terminal.from Z)

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The actual first structural-map equation retains the original cotensor mate. -/
theorem localBoundaryCotensorCorner_π_fst (n : ℕ) (Z : SimplicialPresheaf.{u} D) :
    (localBoundaryCotensorCorner n Z).π ≫ (localBoundaryCotensorCorner n Z).fst =
      (boundaryCotensorMate n).app Z :=
  (localBoundaryCotensorCorner n Z).π_fst

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The actual second structural-map equation retains the original cotensor terminal map. -/
theorem localBoundaryCotensorCorner_π_snd (n : ℕ) (Z : SimplicialPresheaf.{u} D) :
    (localBoundaryCotensorCorner n Z).π ≫ (localBoundaryCotensorCorner n Z).snd =
      ((scalarCotensor (D := D)).obj (op (Δ[n] : SSet.{u}))).map (terminal.from Z) :=
  (localBoundaryCotensorCorner n Z).π_snd

/-- The whole original cotensor boundary test is the supplied corner's structural arrow. -/
def localBoundaryCotensorTest (n : ℕ) (Z : SimplicialPresheaf.{u} D) :
    Arrow (SimplicialPresheaf.{u} D) :=
  Arrow.mk (localBoundaryCotensorCorner n Z).π

private def boundaryWalkingPushout {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι) :
    (parallelPair (boundaryTensorTransformation (D := D) n)
      (boundaryTensorTransformation (D := D) n)).PushoutObjObj WalkingParallelPairHom.left f where
  pt := pp.pt
  inl := pp.inr
  inr := pp.inl
  isPushout := pp.isPushout.flip
  ι := pp.ι
  inl_ι := pp.inr_ι
  inr_ι := pp.inl_ι

/-- Original pushout/terminal squares transpose to the same cotensor corner squares. -/
def localBoundaryCotensorArrowHomEquiv {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ) (Z : SimplicialPresheaf.{u} D)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι) :
    (Arrow.mk pp.ι ⟶ Arrow.mk (terminal.from Z)) ≃
      (Arrow.mk f ⟶ localBoundaryCotensorTest n Z) :=
  Adjunction.leibnizMateArrowHomEquivOf
    (scalarTensorCotensorAdjunction (D := D) ((SSet.boundary.{u} n) : SSet.{u}))
    (scalarTensorCotensorAdjunction (D := D) (Δ[n] : SSet.{u}))
    (boundaryTensorTransformation (D := D) n) f (terminal.from Z)
    (boundaryWalkingPushout f n pp) (localBoundaryCotensorCorner n Z)

/-- Both original diagonal fillers correspond through the actual cotensor transposition. -/
def localBoundaryCotensorLiftStructEquiv {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ) (Z : SimplicialPresheaf.{u} D)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι)
    (a : Arrow.mk pp.ι ⟶ Arrow.mk (terminal.from Z)) :
    Arrow.LiftStruct a ≃
      Arrow.LiftStruct (localBoundaryCotensorArrowHomEquiv f n Z pp a) :=
  Adjunction.leibnizMateLiftStructEquivOf
    (scalarTensorCotensorAdjunction (D := D) ((SSet.boundary.{u} n) : SSet.{u}))
    (scalarTensorCotensorAdjunction (D := D) (Δ[n] : SSet.{u}))
    (boundaryTensorTransformation (D := D) n)
    (boundaryWalkingPushout f n pp) (localBoundaryCotensorCorner n Z) a

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The supplied original boundary pushout lifts exactly against the actual cotensor test. -/
theorem localBoundary_hasLiftingProperty_iff_cotensor {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ) (Z : SimplicialPresheaf.{u} D)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι) :
    HasLiftingProperty pp.ι (terminal.from Z) ↔
      HasLiftingProperty f (localBoundaryCotensorTest n Z).hom :=
  Adjunction.leibnizMate_hasLiftingProperty_iff_of
    (scalarTensorCotensorAdjunction (D := D) ((SSet.boundary.{u} n) : SSet.{u}))
    (scalarTensorCotensorAdjunction (D := D) (Δ[n] : SSet.{u}))
    (boundaryTensorTransformation (D := D) n)
    (boundaryWalkingPushout f n pp) (localBoundaryCotensorCorner n Z)

/-- The actual terminal end corner used for the original raw boundary transposition. -/
def localBoundaryEndCorner {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    innerHomFunctor.PullbackObjObj f (terminal.from Z) :=
  Functor.PullbackObjObj.ofHasPullback _ f (terminal.from Z)

/-- Original scalar boundary squares transpose to the original raw precomposition arrow. -/
def localBoundaryEndArrowHomEquiv {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ) (Z : SimplicialPresheaf.{u} D)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι) :
    (Arrow.mk pp.ι ⟶ Arrow.mk (terminal.from Z)) ≃
      (Arrow.mk (SSet.boundary.{u} n).ι ⟶ Arrow.mk (innerHomPre f Z)) :=
  ((scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp (localBoundaryEndCorner f Z)).trans
    { toFun := fun a => a ≫ (precompCornerIso f Z (localBoundaryEndCorner f Z)).hom
      invFun := fun a => a ≫ (precompCornerIso f Z (localBoundaryEndCorner f Z)).inv
      left_inv := by intro a; simp
      right_inv := by intro a; simp }

/-- Raw end transposition retains both original fillers through the whole terminal Arrow iso. -/
def localBoundaryEndLiftStructEquiv {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ) (Z : SimplicialPresheaf.{u} D)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι)
    (a : Arrow.mk pp.ι ⟶ Arrow.mk (terminal.from Z)) :
    Arrow.LiftStruct a ≃ Arrow.LiftStruct (localBoundaryEndArrowHomEquiv f n Z pp a) :=
  ((scalarTensorHomAdjunction₂ (D := D)).liftStructEquiv pp (localBoundaryEndCorner f Z) a).trans
    (Arrow.liftStructPostcompIsoEquiv
      ((scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp (localBoundaryEndCorner f Z) a)
      (precompCornerIso f Z (localBoundaryEndCorner f Z)))

/-- The original end boundary RLP is the supplied original pushout terminal lifting condition. -/
theorem localBoundary_hasLiftingProperty_iff_end {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (n : ℕ) (Z : SimplicialPresheaf.{u} D)
    (pp : scalarTensor.PushoutObjObj f (SSet.boundary.{u} n).ι) :
    HasLiftingProperty pp.ι (terminal.from Z) ↔
      HasLiftingProperty (SSet.boundary.{u} n).ι (innerHomPre f Z) :=
  ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff
    pp (localBoundaryEndCorner f Z)).trans
      (HasLiftingProperty.iff_of_arrow_iso_right (SSet.boundary.{u} n).ι
        (precompCornerIso f Z (localBoundaryEndCorner f Z)))

/-- Every original local-fibrant target and boundary supplies a literal cotensor right test. -/
def localBoundaryRightTests {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  ofHoms (fun k : {Z : SimplicialPresheaf.{u} D // isOriginalLocalFibrant S Z} × ℕ =>
    (localBoundaryCotensorTest k.2 k.1.val).hom)

/-- Actual base trivial-fibration tests together with all original local boundary right tests. -/
def localWeakRightTests {I : Type i} (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  (monomorphisms (SimplicialPresheaf.{u} D)).rlp ⊔ localBoundaryRightTests S

/-- The original monic local weak class, before any localized model is constructed. -/
def localTrivialMonomorphisms {I : Type i} (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  monomorphisms (SimplicialPresheaf.{u} D) ⊓ originalLocalEquivalences S

private theorem baseTrivialFibrations_llp :
    ((monomorphisms (SimplicialPresheaf.{u} D)).rlp).llp =
      monomorphisms (SimplicialPresheaf.{u} D) := by
  rw [← (data D).cofibrations_eq]
  change (cofibrations (SimplicialPresheaf.{u} D)).rlp.llp =
    cofibrations (SimplicialPresheaf.{u} D)
  rw [cofibrations_rlp, trivialFibrations_llp]

private theorem original_cofibration_of_mono {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (hf : monomorphisms (SimplicialPresheaf.{u} D) f) :
    cofibrations (SimplicialPresheaf.{u} D) f := by
  change (data D).model.categoryWithCofibrations.cofibrations f
  rw [(data D).cofibrations_eq]
  exact hf

/-- The complete original monic local weak class is exactly the internally constructed LLP class. -/
theorem localTrivialMonomorphisms_eq_llp {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    localTrivialMonomorphisms S = (localWeakRightTests S).llp := by
  ext A B f
  constructor
  · rintro ⟨hmono, hweak⟩ X Y p (hbase | hlocal)
    · have hleft : ((monomorphisms (SimplicialPresheaf.{u} D)).rlp).llp f := by
        rw [baseTrivialFibrations_llp]
        exact hmono
      exact hleft p hbase
    · cases hlocal with
      | mk k =>
        let Z := k.1.val
        have hZ : isOriginalLocalFibrant S Z := k.1.property
        let : Fibration (innerHomPre f Z) := (fibration_iff _).mpr
          (rawPrecomp_fibration_of_cofibration f Z (original_cofibration_of_mono f hmono) hZ.1)
        have hI : SSet.modelCategoryQuillen.I.rlp (innerHomPre f Z) :=
          (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mpr
            (hweak Z hZ)
        have hb : HasLiftingProperty (SSet.boundary.{u} k.2).ι (innerHomPre f Z) :=
          hI _ (SSet.modelCategoryQuillen.boundary_ι_mem_I k.2)
        let pp := Functor.PushoutObjObj.ofHasPushout scalarTensor f (SSet.boundary.{u} k.2).ι
        exact (localBoundary_hasLiftingProperty_iff_cotensor f k.2 Z pp).mp
          ((localBoundary_hasLiftingProperty_iff_end f k.2 Z pp).mpr hb)
  · intro h
    have hbase : ((monomorphisms (SimplicialPresheaf.{u} D)).rlp).llp f :=
      fun _ _ p hp => h p (Or.inl hp)
    have hmono : monomorphisms (SimplicialPresheaf.{u} D) f := by
      rw [baseTrivialFibrations_llp] at hbase
      exact hbase
    refine ⟨hmono, ?_⟩
    intro Z hZ
    let : Fibration (innerHomPre f Z) := (fibration_iff _).mpr
      (rawPrecomp_fibration_of_cofibration f Z (original_cofibration_of_mono f hmono) hZ.1)
    apply (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mp
    intro X Y b hb
    cases hb with
    | mk n =>
      have hc : HasLiftingProperty f (localBoundaryCotensorTest n Z).hom :=
        h _ (Or.inr (ofHoms.mk ((⟨Z, hZ⟩ :
          {Z : SimplicialPresheaf.{u} D // isOriginalLocalFibrant S Z}), n)))
      let pp := Functor.PushoutObjObj.ofHasPushout scalarTensor f (SSet.boundary.{u} n).ι
      exact (localBoundary_hasLiftingProperty_iff_end f n Z pp).mp
        ((localBoundary_hasLiftingProperty_iff_cotensor f n Z pp).mpr hc)

/-- Identities and composites remain original monic local weak arrows. -/
theorem localTrivialMonomorphisms_isMultiplicative {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localTrivialMonomorphisms S).IsMultiplicative := by
  rw [localTrivialMonomorphisms_eq_llp]
  infer_instance

/-- Every original Arrow retract of a monic local weak map stays in that class. -/
theorem localTrivialMonomorphisms_isStableUnderRetracts {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localTrivialMonomorphisms S).IsStableUnderRetracts := by
  rw [localTrivialMonomorphisms_eq_llp]
  infer_instance

/-- Pushout along every original map preserves the original monic local weak class. -/
theorem localTrivialMonomorphisms_isStableUnderCobaseChange {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localTrivialMonomorphisms S).IsStableUnderCobaseChange := by
  rw [localTrivialMonomorphisms_eq_llp]
  infer_instance

/-- Value-universe coproducts preserve the original monic local weak class. -/
theorem localTrivialMonomorphisms_isStableUnderCoproducts {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localTrivialMonomorphisms S).IsStableUnderCoproducts.{u} := by
  rw [localTrivialMonomorphisms_eq_llp]
  infer_instance

/-- Every actual continuous value-universe transfinite composite stays monic and locally weak. -/
theorem localTrivialMonomorphisms_isStableUnderTransfiniteComposition {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localTrivialMonomorphisms S).IsStableUnderTransfiniteComposition.{u} := by
  rw [localTrivialMonomorphisms_eq_llp]
  infer_instance

end SimplicialPresheaf.InjectiveKan
