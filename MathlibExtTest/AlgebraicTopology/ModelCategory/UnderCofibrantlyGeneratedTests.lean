/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.UnderCofibrantlyGenerated

/-!
# Tests for fixed-cardinal generation in Under categories
-/

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.UnderCofibrantlyGeneratedTests

#check IsCardinalForSmallObjectArgument.underCostar
#check CofibrantGenerationData.under

section CardinalTransfer

variable {C : Type u} [Category.{v} C]
  (I : MorphismProperty C) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasBinaryCoproducts C] (S : C)
  [HasCoproducts.{w} (Under S)]
  (hI : I.IsCardinalForSmallObjectArgument κ)

example : (I.underCostar S).IsSmall.{w} :=
  (IsCardinalForSmallObjectArgument.underCostar I κ S hI).isSmall

example : LocallySmall.{w} (Under S) :=
  (IsCardinalForSmallObjectArgument.underCostar I κ S hI).locallySmall

example : HasPushouts (Under S) :=
  (IsCardinalForSmallObjectArgument.underCostar I κ S hI).hasPushouts

example : HasCoproducts.{w} (Under S) :=
  (IsCardinalForSmallObjectArgument.underCostar I κ S hI).hasCoproducts

example : HasIterationOfShape κ.ord.ToType (Under S) :=
  (IsCardinalForSmallObjectArgument.underCostar I κ S hI).hasIterationOfShape

example {A B X Y : Under S} (i : A ⟶ B)
    (hi : (I.underCostar S) i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => (I.underCostar S).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  let h := IsCardinalForSmallObjectArgument.underCostar I κ S hI
  exact h.preservesColimit i hi f hf

example (A : C) (X : Under S) :
    ((Under.costar S).obj A ⟶ X) ≃ (A ⟶ X.right) :=
  (Under.costarAdjForget S).homEquiv A X

example (A : C) (X : Under S) (f : (Under.costar S).obj A ⟶ X) :
    ((Under.costarAdjForget S).homEquiv A X).symm
      ((Under.costarAdjForget S).homEquiv A X f) = f :=
  Equiv.symm_apply_apply _ _

example : HasPushouts (Under S) := by
  let _ : HasPushouts C := hI.hasPushouts
  infer_instance

example : HasIterationOfShape κ.ord.ToType (Under S) := by
  let _ : HasIterationOfShape κ.ord.ToType C := hI.hasIterationOfShape
  constructor
  · intro j hj
    let _ : HasColimitsOfShape (Set.Iio j) C :=
      hasColimitsOfShape_of_isSuccLimit C j hj
    let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    let _ : IsFiltered (Set.Iio j) := inferInstance
    let _ : IsConnected (Set.Iio j) := inferInstance
    infer_instance
  · let _ : HasColimitsOfShape κ.ord.ToType C := inferInstance
    let _ : Nonempty κ.ord.ToType := inferInstance
    let _ : IsFiltered κ.ord.ToType := inferInstance
    let _ : IsConnected κ.ord.ToType := inferInstance
    infer_instance

example : PreservesWellOrderContinuousOfShape κ.ord.ToType
    (Under.forget S) := by
  let _ : PreservesFilteredColimitsOfSize.{w, w} (Under.forget S) :=
    inferInstance
  exact
    { preservesColimitsOfShape := fun j hj => by
        let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
        let _ : IsFiltered (Set.Iio j) := inferInstance
        infer_instance }

example : PreservesColimitsOfShape κ.ord.ToType (Under.forget S) := by
  let _ : PreservesFilteredColimitsOfSize.{w, w} (Under.forget S) :=
    inferInstance
  let _ : Nonempty κ.ord.ToType := inferInstance
  let _ : IsFiltered κ.ord.ToType := inferInstance
  infer_instance

example : True := by
  fail_if_success
    let _ : (I.underCostar S).HasSmallObjectArgument.{w} := inferInstance
  fail_if_success
    let _ : PreservesColimitsOfSize.{w, w} (Under.forget S) :=
      inferInstance
  trivial

end CardinalTransfer

section PushoutCancellation

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  {S A B : C} (g : A ⟶ B)
  {X Y : Under S}
  (a : (Under.costar S).obj A ⟶ X)
  (b : (Under.costar S).obj B ⟶ Y)
  (f : X ⟶ Y)

private abbrev baseTop : A ⟶ X.right :=
  (Under.costarAdjForget S).homEquiv A X a

private abbrev baseBottom : B ⟶ Y.right :=
  (Under.costarAdjForget S).homEquiv B Y b

example (h : IsPushout a ((Under.costar S).map g) f b) :
    IsPushout (baseTop a) g f.right (baseBottom b) := by
  have hcomm : baseTop a ≫ f.right = g ≫ baseBottom b := by
    have hw := congrArg
      (fun k => (Under.costarAdjForget S).homEquiv A Y k) h.w
    rw [(Under.costarAdjForget S).homEquiv_naturality_right,
      (Under.costarAdjForget S).homEquiv_naturality_left] at hw
    simpa [baseTop, baseBottom] using hw
  refine { w := hcomm, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk hcomm ?desc ?facLeft ?facRight ?uniq
  · intro s
    let Z : Under S := Under.mk (X.hom ≫ s.inl)
    let p : X ⟶ Z := Under.homMk s.inl rfl
    let q : (Under.costar S).obj B ⟶ Z :=
      ((Under.costarAdjForget S).homEquiv B Z).symm s.inr
    have w : a ≫ p = (Under.costar S).map g ≫ q := by
      apply ((Under.costarAdjForget S).homEquiv A Z).injective
      rw [(Under.costarAdjForget S).homEquiv_naturality_right,
        (Under.costarAdjForget S).homEquiv_naturality_left]
      have hp : (Under.forget S).map p = s.inl := rfl
      have hq : (Under.costarAdjForget S).homEquiv B Z q = s.inr :=
        Equiv.apply_symm_apply _ _
      rw [hp, hq]
      exact s.condition
    exact (h.desc p q w).right
  · intro s
    let Z : Under S := Under.mk (X.hom ≫ s.inl)
    let p : X ⟶ Z := Under.homMk s.inl rfl
    let q : (Under.costar S).obj B ⟶ Z :=
      ((Under.costarAdjForget S).homEquiv B Z).symm s.inr
    have w : a ≫ p = (Under.costar S).map g ≫ q := by
      apply ((Under.costarAdjForget S).homEquiv A Z).injective
      rw [(Under.costarAdjForget S).homEquiv_naturality_right,
        (Under.costarAdjForget S).homEquiv_naturality_left]
      have hp : (Under.forget S).map p = s.inl := rfl
      have hq : (Under.costarAdjForget S).homEquiv B Z q = s.inr :=
        Equiv.apply_symm_apply _ _
      rw [hp, hq]
      exact s.condition
    have hw : f.right ≫ (h.desc p q w).right = p.right :=
      congrArg Under.Hom.right (h.inl_desc p q w)
    change f.right ≫ (h.desc p q w).right = s.inl
    exact hw.trans rfl
  · intro s
    let Z : Under S := Under.mk (X.hom ≫ s.inl)
    let p : X ⟶ Z := Under.homMk s.inl rfl
    let q : (Under.costar S).obj B ⟶ Z :=
      ((Under.costarAdjForget S).homEquiv B Z).symm s.inr
    have w : a ≫ p = (Under.costar S).map g ≫ q := by
      apply ((Under.costarAdjForget S).homEquiv A Z).injective
      rw [(Under.costarAdjForget S).homEquiv_naturality_right,
        (Under.costarAdjForget S).homEquiv_naturality_left]
      have hp : (Under.forget S).map p = s.inl := rfl
      have hq : (Under.costarAdjForget S).homEquiv B Z q = s.inr :=
        Equiv.apply_symm_apply _ _
      rw [hp, hq]
      exact s.condition
    have hw := congrArg
      (fun k => (Under.costarAdjForget S).homEquiv B Z k)
      (h.inr_desc p q w)
    rw [(Under.costarAdjForget S).homEquiv_naturality_right] at hw
    have hq : (Under.costarAdjForget S).homEquiv B Z q = s.inr :=
      Equiv.apply_symm_apply _ _
    have hd : (Under.forget S).map (h.desc p q w) =
        (h.desc p q w).right := rfl
    rw [hq, hd] at hw
    exact hw
  · intro s m hmLeft hmRight
    let Z : Under S := Under.mk (X.hom ≫ s.inl)
    let p : X ⟶ Z := Under.homMk s.inl rfl
    let q : (Under.costar S).obj B ⟶ Z :=
      ((Under.costarAdjForget S).homEquiv B Z).symm s.inr
    have w : a ≫ p = (Under.costar S).map g ≫ q := by
      apply ((Under.costarAdjForget S).homEquiv A Z).injective
      rw [(Under.costarAdjForget S).homEquiv_naturality_right,
        (Under.costarAdjForget S).homEquiv_naturality_left]
      have hp : (Under.forget S).map p = s.inl := rfl
      have hq : (Under.costarAdjForget S).homEquiv B Z q = s.inr :=
        Equiv.apply_symm_apply _ _
      rw [hp, hq]
      exact s.condition
    let m' : Y ⟶ Z := Under.homMk m (by
      dsimp [Z]
      rw [← Under.w f, Category.assoc, hmLeft])
    have hm' : m' = h.desc p q w := by
      apply h.hom_ext
      · apply Under.UnderMorphism.ext
        simpa [m', p] using hmLeft
      · apply ((Under.costarAdjForget S).homEquiv B Z).injective
        rw [(Under.costarAdjForget S).homEquiv_naturality_right,
          (Under.costarAdjForget S).homEquiv_naturality_right]
        have hm : (Under.forget S).map m' = m := rfl
        have hd : (Under.forget S).map (h.desc p q w) =
            (h.desc p q w).right := rfl
        rw [hm, hd]
        have hr := congrArg
          (fun k => (Under.costarAdjForget S).homEquiv B Z k)
          (h.inr_desc p q w)
        rw [(Under.costarAdjForget S).homEquiv_naturality_right] at hr
        have hq : (Under.costarAdjForget S).homEquiv B Z q = s.inr :=
          Equiv.apply_symm_apply _ _
        rw [hq, hd] at hr
        exact hmRight.trans hr.symm
    exact congrArg Under.Hom.right hm'

end PushoutCancellation

section MissingCoproductPremise

variable {C : Type u} [Category.{v} C]
  (I : MorphismProperty C) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasBinaryCoproducts C] (S : C)
  (hI : I.IsCardinalForSmallObjectArgument κ)

example : True := by
  fail_if_success
    exact IsCardinalForSmallObjectArgument.underCostar I κ S hI
  trivial

end MissingCoproductPremise

section GenerationData

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (G : CofibrantGenerationData C κ) (S : C)
  [HasCoproducts.{w} (Under S)]

example : (CofibrantGenerationData.under κ G S).I =
    G.I.underCostar S := rfl

example : (CofibrantGenerationData.under κ G S).J =
    G.J.underCostar S := rfl

example : IsCardinalForSmallObjectArgument
    (CofibrantGenerationData.under κ G S).I κ :=
  (CofibrantGenerationData.under κ G S).I_smallObject

example : IsCardinalForSmallObjectArgument
    (CofibrantGenerationData.under κ G S).J κ :=
  (CofibrantGenerationData.under κ G S).J_smallObject

example : (CofibrantGenerationData.under κ G S).I.rlp =
    trivialFibrations (Under S) :=
  (CofibrantGenerationData.under κ G S).I_rlp

example : (CofibrantGenerationData.under κ G S).J.rlp =
    fibrations (Under S) :=
  (CofibrantGenerationData.under κ G S).J_rlp

example : HasSmallObjectArgument.{w}
    (CofibrantGenerationData.under κ G S).I := by
  exact ⟨κ, inferInstance, inferInstance,
    (CofibrantGenerationData.under κ G S).I_smallObject⟩

example : HasSmallObjectArgument.{w}
    (CofibrantGenerationData.under κ G S).J := by
  exact ⟨κ, inferInstance, inferInstance,
    (CofibrantGenerationData.under κ G S).J_smallObject⟩

example : HasFunctorialFactorization
    (CofibrantGenerationData.under κ G S).I.rlp.llp
    (CofibrantGenerationData.under κ G S).I.rlp := by
  let _ : HasSmallObjectArgument.{w}
      (CofibrantGenerationData.under κ G S).I :=
    ⟨κ, inferInstance, inferInstance,
      (CofibrantGenerationData.under κ G S).I_smallObject⟩
  infer_instance

example : HasFunctorialFactorization
    (CofibrantGenerationData.under κ G S).J.rlp.llp
    (CofibrantGenerationData.under κ G S).J.rlp := by
  let _ : HasSmallObjectArgument.{w}
      (CofibrantGenerationData.under κ G S).J :=
    ⟨κ, inferInstance, inferInstance,
      (CofibrantGenerationData.under κ G S).J_smallObject⟩
  infer_instance

end GenerationData

section Universes

#check @IsCardinalForSmallObjectArgument.underCostar.{0, 0, 0}
#check @IsCardinalForSmallObjectArgument.underCostar.{1, 1, 1}
#check @IsCardinalForSmallObjectArgument.underCostar.{0, 1, 1}
#check @IsCardinalForSmallObjectArgument.underCostar.{1, 0, 1}
#check @IsCardinalForSmallObjectArgument.underCostar.{1, 1, 0}
#check @IsCardinalForSmallObjectArgument.underCostar.{w, v, u}

#check @CofibrantGenerationData.under.{0, 0, 0}
#check @CofibrantGenerationData.under.{1, 1, 1}
#check @CofibrantGenerationData.under.{0, 1, 1}
#check @CofibrantGenerationData.under.{1, 0, 1}
#check @CofibrantGenerationData.under.{1, 1, 0}
#check @CofibrantGenerationData.under.{w, v, u}

end Universes

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check strictMapPreimage_exists

#guard_msgs (error, substring := true) in
#check costarCoyonedaIso

#guard_msgs (error, substring := true) in
#check forgetAttachCellsUnderCostar

#guard_msgs (error, substring := true) in
#check forgetRelativeCellComplexUnderCostar

#guard_msgs (error, substring := true) in
#check preservesColimit_underCostar

#guard_msgs (error, substring := true) in
#check PointedCGWH.cofibrantGenerationData

end PrivacyAndNonclaims

#print axioms IsCardinalForSmallObjectArgument.underCostar
#print axioms CofibrantGenerationData.under

end MathlibExtTest.UnderCofibrantlyGeneratedTests
