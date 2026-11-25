/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
public import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure
public import Mathlib.CategoryTheory.Presentable.SolutionSetCondition
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Presentable.IsDiscrete
import Mathlib.Order.SuccPred.Basic

/-!
# Smith recognition

This file proves Beke--Smith recognition from a small generating family,
closure of the candidate trivial cofibrations and a solution set at the
generators. It returns explicit weak-factorization data and installs no model
structure on the raw carrier.

The source is Tibor Beke, *Sheafifiable homotopy model categories*,
Math. Proc. Cambridge Philos. Soc. 129 (2000), Theorem 1.7, which records
Jeff Smith's recognition theorem. Beke states the generatorwise solution-set
condition directly as hypothesis (c3); `SmithRecognitionInput.solution_set`
records that condition at the chosen generators. Accessibility gives a common
sufficient condition for solution sets. The conclusion here is explicit
weak-factorization and class data. The generating-family proof factors each
supplied weak solution arrow once and interpolates incoming generator squares
through its right factor; this is a proof variation of Beke's Lemma 1.9.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- Result-free hypotheses for Beke--Smith recognition. The solution-set
condition is required only at the chosen generating arrows. -/
structure SmithRecognitionInput (I W : MorphismProperty C) : Prop where
  weak_two_out_of_three : W.HasTwoOutOfThreeProperty
  weak_retracts : W.IsStableUnderRetracts
  trivial_fibrations_weak : I.rlp ≤ W
  trivial_cofibrations_cobase :
    (I.rlp.llp ⊓ W).IsStableUnderCobaseChange
  trivial_cofibrations_transfinite :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (I.rlp.llp ⊓ W)
  solution_set :
    ∀ {A B : C} (i : A ⟶ B), I i →
      ∃ (ι : Type w)
        (X : ι → W.arrowObjectProperty.FullSubcategory)
        (f : ∀ k, Arrow.mk i ⟶ W.arrowObjectProperty.ι.obj (X k)),
        ∀ (Y : W.arrowObjectProperty.FullSubcategory)
          (h : Arrow.mk i ⟶ W.arrowObjectProperty.ι.obj Y),
          ∃ (k : ι) (g : X k ⟶ Y),
            f k ≫ W.arrowObjectProperty.ι.map g = h

/-- Explicit classes and weak factorization systems produced by Smith
recognition. In particular, the trivial-fibration equality is a conclusion. -/
structure SmithModelStructureData (I W : MorphismProperty C) where
  /-- A chosen generating family of trivial cofibrations. -/
  J : MorphismProperty C
  J_smallObject : J.HasSmallObjectArgument.{w}
  cofibration_wfs :
    MorphismProperty.IsWeakFactorizationSystem I.rlp.llp I.rlp
  trivialCofibration_wfs :
    MorphismProperty.IsWeakFactorizationSystem J.rlp.llp J.rlp
  trivialCofibrations_eq : J.rlp.llp = I.rlp.llp ⊓ W
  fibrations_eq : J.rlp = (I.rlp.llp ⊓ W).rlp
  trivialFibrations_eq : J.rlp ⊓ W = I.rlp

private noncomputable def smithSolutionSetFamily
    (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    (h : SmithRecognitionInput.{w} (C := C) I W) :
    Σ (ι : Type w) (A B : ι → C),
      { j : ∀ k, A k ⟶ B k //
        (∀ k, (I.rlp.llp ⊓ W) (j k)) ∧
        (∀ {A₀ B₀ X Y : C} (i : A₀ ⟶ B₀), I i →
          (p : X ⟶ Y) → W p → (sq : Arrow.mk i ⟶ Arrow.mk p) →
          ∃ (k : ι) (u : Arrow.mk i ⟶ Arrow.mk (j k))
            (v : Arrow.mk (j k) ⟶ Arrow.mk p), u ≫ v = sq) } := by
  let _ : W.HasTwoOutOfThreeProperty := h.weak_two_out_of_three
  let hex := HasSmallObjectArgument.exists_cardinal (I := I)
  let κI := hex.choose
  let hκI := hex.choose_spec.choose
  let hbotI := hex.choose_spec.choose_spec.choose
  let hI := hex.choose_spec.choose_spec.choose_spec
  let _ : Fact κI.IsRegular := hκI
  let _ : OrderBot κI.ord.ToType := hbotI
  let _ : I.IsCardinalForSmallObjectArgument κI := hI
  let _ : I.IsSmall.{w} := hI.isSmall
  let S := Shrink.{w} I.toSet
  let rep : S → I.toSet := (equivShrink _).symm
  let sol (s : S) := h.solution_set (rep s).1.hom (rep s).2
  let solIndex (s : S) : Type w := (sol s).choose
  let solObj (s : S) : solIndex s → W.arrowObjectProperty.FullSubcategory :=
    (sol s).choose_spec.choose
  let solSq (s : S) (k : solIndex s) :
      Arrow.mk (rep s).1.hom ⟶ W.arrowObjectProperty.ι.obj (solObj s k) :=
    (sol s).choose_spec.choose_spec.choose k
  let solUniversal (s : S) :=
    (sol s).choose_spec.choose_spec.choose_spec
  let data := functorialFactorizationData I.rlp.llp I.rlp
  let factor (k : Σ s, solIndex s) :=
    data.factorizationData (solObj k.1 k.2).obj.hom
  let A : (Σ s, solIndex s) → C := fun k => (solObj k.1 k.2).obj.left
  let B : (Σ s, solIndex s) → C := fun k => (factor k).Z
  let j : ∀ k, A k ⟶ B k := fun k => (factor k).i
  refine ⟨(Σ s, solIndex s), A, B, ⟨j, ?_, ?_⟩⟩
  · intro k
    have hpW : W (factor k).p := h.trivial_fibrations_weak _ (factor k).hp
    have hcomp : W ((factor k).i ≫ (factor k).p) := by
      rw [(factor k).fac]
      exact (solObj k.1 k.2).property
    exact ⟨(factor k).hi, W.of_postcomp _ _ hpW hcomp⟩
  · intro A₀ B₀ X Y i hi p hp sq
    let s : S := equivShrink _ ⟨Arrow.mk i, hi⟩
    let Y' : W.arrowObjectProperty.FullSubcategory := ⟨Arrow.mk p, hp⟩
    let eRep : Arrow.mk (rep s).1.hom ≅ Arrow.mk i :=
      eqToIso (by simp [s, rep])
    let sq' : Arrow.mk (rep s).1.hom ⟶
        W.arrowObjectProperty.ι.obj Y' := eRep.hom ≫ sq
    obtain ⟨k, g, hg⟩ := solUniversal s Y' sq'
    let sq₀ : Arrow.mk i ⟶ W.arrowObjectProperty.ι.obj (solObj s k) :=
      eRep.inv ≫ solSq s k
    let d := factor ⟨s, k⟩
    let _ : HasLiftingProperty i d.p := d.hp _ hi
    let liftSq : CommSq (sq₀.left ≫ d.i) i d.p sq₀.right :=
      ⟨by rw [Category.assoc, d.fac]; exact sq₀.w⟩
    let u : Arrow.mk i ⟶ Arrow.mk d.i :=
      Arrow.homMk sq₀.left liftSq.lift (by simp)
    let toWeak : Arrow.mk d.i ⟶
        W.arrowObjectProperty.ι.obj (solObj s k) :=
      Arrow.homMk (𝟙 _) d.p (by simp [d.fac])
    let v : Arrow.mk d.i ⟶ Arrow.mk p :=
      toWeak ≫ W.arrowObjectProperty.ι.map g
    refine ⟨⟨s, k⟩, u, v, ?_⟩
    calc
      u ≫ v = sq₀ ≫ W.arrowObjectProperty.ι.map g := by
        ext <;> simp [u, v, toWeak]
      _ = eRep.inv ≫ (solSq s k ≫ W.arrowObjectProperty.ι.map g) := by
        simp [sq₀]
      _ = eRep.inv ≫ sq' := by rw [hg]
      _ = sq := by simp [sq', eRep]

private theorem smithGeneratingTrivialCofibrations
    (I W : MorphismProperty C) [IsLocallyPresentable.{w} C]
    [I.HasSmallObjectArgument.{w}]
    (h : SmithRecognitionInput.{w} (C := C) I W) :
    Nonempty (Σ J : MorphismProperty C,
      { _hJ : J.HasSmallObjectArgument.{w} //
        J ≤ I.rlp.llp ⊓ W ∧ J.rlp ⊓ W ≤ I.rlp }) := by
  let family := smithSolutionSetFamily I W h
  let ι := family.1
  let A := family.2.1
  let B := family.2.2.1
  let j := family.2.2.2.1
  let hmem := family.2.2.2.2.1
  let hfactor :
      ∀ {A₀ B₀ X Y : C} (i : A₀ ⟶ B₀), I i →
        (p : X ⟶ Y) → W p → (sq : Arrow.mk i ⟶ Arrow.mk p) →
        ∃ (k : ι) (u : Arrow.mk i ⟶ Arrow.mk (j k))
          (v : Arrow.mk (j k) ⟶ Arrow.mk p), u ≫ v = sq :=
    family.2.2.2.2.2
  let J : MorphismProperty C := MorphismProperty.ofHoms j
  let _ : J.IsSmall.{w} := MorphismProperty.isSmall_ofHoms j
  obtain ⟨κ₀, hκ₀, hC₀⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  let _ : Fact κ₀.IsRegular := hκ₀
  let _ : IsCardinalLocallyPresentable C κ₀ := hC₀
  let D₀ : Type := Discrete PUnit
  let K := J.toSet
  let _ : Small.{w} K := inferInstance
  let source : K → C := fun k => k.1.left
  let F : K → D₀ ⥤ C := fun k => (Functor.const D₀).obj (source k)
  let _ (k : K) : Functor.IsAccessible.{w} (F k) := by
    dsimp [F]
    infer_instance
  obtain ⟨κ, hκ, hD₀, hC, _, hPres⟩ :=
    IsCardinalAccessibleCategory.uniformization_of_small F
  let _ : Fact κ.IsRegular := hκ
  let _ : IsCardinalAccessibleCategory D₀ κ := hD₀
  let _ : IsCardinalAccessibleCategory C κ := hC
  let hCLP : IsCardinalLocallyPresentable C κ :=
    { toHasCardinalFilteredGenerator := inferInstance
      toHasColimitsOfSize := inferInstance }
  have hne : Nonempty κ.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero Fact.out
  let _ : Nonempty κ.ord.ToType := hne
  let hBot : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let _ : OrderBot κ.ord.ToType := hBot
  have hSource (k : K) : IsCardinalPresentable (source k) κ := by
    let _ : (F k).PreservesCardinalPresentable κ := hPres k
    have hp : IsCardinalPresentable ((F k).obj ⟨PUnit.unit⟩) κ :=
      inferInstance
    simpa [F] using hp
  let hJκ : J.IsCardinalForSmallObjectArgument κ :=
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A₀ B₀ X Y f hf g hg
        let k : K := ⟨Arrow.mk f, hf⟩
        have hA : IsCardinalPresentable A₀ κ := by
          simpa [k, source] using hSource k
        let _ : IsCardinalPresentable A₀ κ := hA
        let _ : PreservesColimitsOfShape κ.ord.ToType
            (coyoneda.obj (Opposite.op A₀)) :=
          preservesColimitsOfShape_of_isCardinalPresentable
            A₀ κ κ.ord.ToType
        infer_instance }
  let hJSOA : J.HasSmallObjectArgument.{w} :=
    ⟨κ, inferInstance, hBot, hJκ⟩
  have hJ_le : J ≤ I.rlp.llp ⊓ W := by
    intro X Y f hf
    change MorphismProperty.ofHoms j f at hf
    rw [MorphismProperty.ofHoms_iff] at hf
    obtain ⟨k, hk⟩ := hf
    rw [← (I.rlp.llp ⊓ W).arrow_mk_mem_toSet_iff, hk,
      MorphismProperty.arrow_mk_mem_toSet_iff]
    exact hmem k
  have hsolution : J.rlp ⊓ W ≤ I.rlp := by
    intro X Y p hp A₀ B₀ i hi
    refine ⟨fun {f} {g} sq => ?_⟩
    let sqArrow : Arrow.mk i ⟶ Arrow.mk p := Arrow.homMk f g sq.w
    obtain ⟨k, u, v, huv⟩ := hfactor i hi p hp.2 sqArrow
    let _ : HasLiftingProperty (j k) p := hp.1 _ (MorphismProperty.ofHoms.mk k)
    let vsq : CommSq v.left (j k) p v.right := ⟨v.w⟩
    let liftData : vsq.LiftStruct :=
      (inferInstance : vsq.HasLift).exists_lift.some
    apply CommSq.HasLift.mk'
    refine
      { l := u.right ≫ liftData.l
        fac_left := ?_
        fac_right := ?_ }
    · have hu : u.left ≫ j k = i ≫ u.right := u.w
      rw [← Category.assoc, ← hu, Category.assoc, liftData.fac_left]
      have huv_left := congrArg Arrow.Hom.left huv
      simpa [sqArrow] using huv_left
    · rw [Category.assoc, liftData.fac_right]
      have huv_right := congrArg Arrow.Hom.right huv
      simpa [sqArrow] using huv_right
  exact ⟨⟨J, ⟨hJSOA, hJ_le, hsolution⟩⟩⟩

private noncomputable def smithTrivialFibrationRetract
    (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    (h : SmithRecognitionInput.{w} (C := C) I W)
    {J : MorphismProperty C}
    (hleft : J.rlp.llp = I.rlp.llp ⊓ W)
    {X Y : C} (f : X ⟶ Y) (hf : (J.rlp ⊓ W) f) :
    Σ p : I.rlp.arrowObjectProperty.FullSubcategory,
      RetractArrow f p.obj.hom := by
  let _ : W.HasTwoOutOfThreeProperty := h.weak_two_out_of_three
  let d := factorizationData I.rlp.llp I.rlp f
  have hpW : W d.p := h.trivial_fibrations_weak _ d.hp
  have hcomp : W (d.i ≫ d.p) := by rw [d.fac]; exact hf.2
  have hiW : W d.i := W.of_postcomp _ _ hpW hcomp
  have hiJ : J.rlp.llp d.i := by
    rw [hleft]
    exact ⟨d.hi, hiW⟩
  let _ : HasLiftingProperty d.i f := hiJ _ hf.1
  exact ⟨⟨Arrow.mk d.p, d.hp⟩, RetractArrow.ofRightLiftingProperty d.fac⟩

private theorem smithTrivialFibrations_eq_aux
    (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    (h : SmithRecognitionInput.{w} (C := C) I W)
    {J : MorphismProperty C}
    (hleft : J.rlp.llp = I.rlp.llp ⊓ W) :
    J.rlp ⊓ W = I.rlp := by
  apply le_antisymm
  · intro X Y f hf
    obtain ⟨p, hp⟩ := smithTrivialFibrationRetract I W h hleft f hf
    exact I.rlp.of_retract hp p.property
  · intro X Y p hp
    refine ⟨?_, h.trivial_fibrations_weak _ hp⟩
    intro A B j hj
    have hj' : J.rlp.llp j := J.le_llp_rlp _ hj
    rw [hleft] at hj'
    exact hj'.1 _ hp

/-- Beke, Theorem 1.7 (Jeff Smith recognition), in the explicit
solution-set-at-generators formulation described in the module docstring. -/
theorem smithRecognition
    (I W : MorphismProperty C) [IsLocallyPresentable.{w} C]
    [I.HasSmallObjectArgument.{w}]
    (h : SmithRecognitionInput.{w} (C := C) I W) :
    Nonempty (SmithModelStructureData.{w} (C := C) I W) := by
  let T := I.rlp.llp ⊓ W
  let _ : W.HasTwoOutOfThreeProperty := h.weak_two_out_of_three
  let _ : W.IsStableUnderRetracts := h.weak_retracts
  let _ : T.IsStableUnderCobaseChange := h.trivial_cofibrations_cobase
  let _ : T.IsStableUnderTransfiniteComposition.{w} :=
    h.trivial_cofibrations_transfinite
  have hCoproduct : T.IsStableUnderCoproducts.{w} := by
    obtain ⟨κ₀, hκ₀, hC₀⟩ := IsLocallyPresentable.exists_cardinal.{w} C
    let _ : Fact κ₀.IsRegular := hκ₀
    let _ : IsCardinalLocallyPresentable C κ₀ := hC₀
    exact T.isStableUnderCoproducts_of_cobase_transfinite
  let _ : T.IsStableUnderCoproducts.{w} := hCoproduct
  obtain ⟨⟨J, hJ⟩⟩ := smithGeneratingTrivialCofibrations I W h
  let hJSOA : J.HasSmallObjectArgument.{w} := hJ.1
  let hJle : J ≤ T := hJ.2.1
  let hsolution : J.rlp ⊓ W ≤ I.rlp := hJ.2.2
  let _ : J.HasSmallObjectArgument.{w} := hJSOA
  let _ : T.IsStableUnderRetracts := by
    change (I.rlp.llp ⊓ W).IsStableUnderRetracts
    infer_instance
  have hleft_le : J.rlp.llp ≤ T := by
    rw [J.llp_rlp_of_hasSmallObjectArgument]
    refine (MorphismProperty.retracts_le_iff
      (P := MorphismProperty.transfiniteCompositions.{w}
        (MorphismProperty.coproducts.{w} J).pushouts) (Q := T)).2 ?_
    refine (MorphismProperty.transfiniteCompositions_le_iff
      (P := (MorphismProperty.coproducts.{w} J).pushouts) (Q := T)).2 ?_
    refine (MorphismProperty.pushouts_le_iff
      (P := MorphismProperty.coproducts.{w} J) (Q := T)).2 ?_
    refine (MorphismProperty.coproducts_le_iff (P := J) (Q := T)).2 ?_
    exact hJle
  have hle_left : T ≤ J.rlp.llp := by
    intro X Y f hf
    let d := factorizationData J.rlp.llp J.rlp f
    have hdiT : T d.i := hleft_le _ d.hi
    have hcomp : W (d.i ≫ d.p) := by rw [d.fac]; exact hf.2
    have hdpW : W d.p := W.of_precomp _ _ hdiT.2 hcomp
    have hdpI : I.rlp d.p := hsolution _ ⟨d.hp, hdpW⟩
    let _ : HasLiftingProperty f d.p := hf.1 _ hdpI
    exact J.rlp.llp.of_retract
      (RetractArrow.ofLeftLiftingProperty d.fac) d.hi
  have hleft : J.rlp.llp = T := le_antisymm hleft_le hle_left
  have hright : J.rlp = T.rlp := by
    calc
      J.rlp = J.rlp.llp.rlp := J.rlp_llp_rlp.symm
      _ = T.rlp := congrArg MorphismProperty.rlp hleft
  have hIWfs : MorphismProperty.IsWeakFactorizationSystem
      I.rlp.llp I.rlp :=
    MorphismProperty.IsWeakFactorizationSystem.mk' _ _
      (fun _ _ hi hp => hi _ hp)
  have hJWfs : MorphismProperty.IsWeakFactorizationSystem
      J.rlp.llp J.rlp :=
    MorphismProperty.IsWeakFactorizationSystem.mk' _ _
      (fun _ _ hi hp => hi _ hp)
  have hthird : J.rlp ⊓ W = I.rlp :=
    smithTrivialFibrations_eq_aux I W h hleft
  exact ⟨{
    J := J
    J_smallObject := hJSOA
    cofibration_wfs := hIWfs
    trivialCofibration_wfs := hJWfs
    trivialCofibrations_eq := hleft
    fibrations_eq := hright
    trivialFibrations_eq := hthird }⟩

/-- Accessible and accessibly embedded candidate weak maps supply the
solution-set hypothesis in Smith recognition. -/
theorem smithRecognition_of_accessible
    (I W : MorphismProperty C) [IsLocallyPresentable.{w} C]
    [I.HasSmallObjectArgument.{w}] [W.IsAccessible.{w}]
    (weak_two_out_of_three : W.HasTwoOutOfThreeProperty)
    (weak_retracts : W.IsStableUnderRetracts)
    (trivial_fibrations_weak : I.rlp ≤ W)
    (trivial_cofibrations_cobase :
      (I.rlp.llp ⊓ W).IsStableUnderCobaseChange)
    (trivial_cofibrations_transfinite :
      MorphismProperty.IsStableUnderTransfiniteComposition.{w}
        (I.rlp.llp ⊓ W)) :
    Nonempty (SmithModelStructureData.{w} (C := C) I W) := by
  obtain ⟨κ, hκ, hWκ⟩ :=
    MorphismProperty.IsAccessible.exists_cardinal (W := W)
  let _ : Fact κ.IsRegular := hκ
  let _ : W.IsCardinalAccessible κ := hWκ
  let _ : IsAccessibleCategory.{w}
      W.arrowObjectProperty.FullSubcategory :=
    { exists_cardinal := ⟨κ, hκ, inferInstance⟩ }
  let _ : Functor.IsAccessible.{w} W.arrowObjectProperty.ι :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  have hsol : SolutionSetCondition.{w} W.arrowObjectProperty.ι :=
    SolutionSetCondition.of_isCardinalAccessible W.arrowObjectProperty.ι
  apply smithRecognition I W
  exact
    { weak_two_out_of_three := weak_two_out_of_three
      weak_retracts := weak_retracts
      trivial_fibrations_weak := trivial_fibrations_weak
      trivial_cofibrations_cobase := trivial_cofibrations_cobase
      trivial_cofibrations_transfinite := trivial_cofibrations_transfinite
      solution_set := by
        intro A B i hi
        exact hsol (Arrow.mk i) }

end HomotopicalAlgebra
