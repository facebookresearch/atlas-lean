/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.UnderCombinatorial
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Fixed-cardinal cofibrant generation in Under categories

Costar images preserve a specified small-object cardinal.  Consequently,
explicit cofibrant-generation data transfers to an Under category at the
same cardinal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe t w v v' u u'

open CategoryTheory CategoryTheory.Limits
open HomotopicalAlgebra

namespace CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument

private theorem strictMapPreimage_exists
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (I : MorphismProperty C) (F : C ⥤ D)
    {X Y : D} {f : X ⟶ Y} (hf : (I.strictMap F) f) :
    ∃ q : I.toSet,
      Nonempty (CategoryTheory.Arrow.mk f ≅
        CategoryTheory.Arrow.mk (F.map q.1.hom)) := by
  cases hf with
  | @map X' Y' g hg =>
      exact ⟨⟨CategoryTheory.Arrow.mk g, hg⟩, ⟨Iso.refl _⟩⟩

private noncomputable def costarCoyonedaIso
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (S A : C) :
    CategoryTheory.Under.forget S ⋙ coyoneda.obj (Opposite.op A) ≅
      coyoneda.obj (Opposite.op ((CategoryTheory.Under.costar S).obj A)) :=
  ((CategoryTheory.Under.costarAdjForget S).compCoyonedaIso.app (Opposite.op A)).symm

private noncomputable def forgetAttachCellsUnderCostar
    {C : Type u} [Category.{v} C]
    [HasBinaryCoproducts C] [HasCoproducts.{w} C]
    (S : C) {α : Type t} {A B : α → C}
    (g : ∀ a, A a ⟶ B a)
    {X Y : CategoryTheory.Under S} {f : X ⟶ Y}
    (c : AttachCells.{w} (fun a => (CategoryTheory.Under.costar S).map (g a)) f) :
    AttachCells.{w} g f.right := by
  let A' : c.ι → C := fun i => A (c.π i)
  let B' : c.ι → C := fun i => B (c.π i)
  let cofanA : Cofan A' := colimit.cocone (Discrete.functor A')
  let cofanB : Cofan B' := colimit.cocone (Discrete.functor B')
  let hA : IsColimit cofanA := colimit.isColimit (Discrete.functor A')
  let hB : IsColimit cofanB := colimit.isColimit (Discrete.functor B')
  let dA : Discrete.functor (fun i => (CategoryTheory.Under.costar S).obj (A' i)) ≅
      Discrete.functor A' ⋙ CategoryTheory.Under.costar S :=
    Discrete.natIso (fun _ => Iso.refl _)
  let dB : Discrete.functor (fun i => (CategoryTheory.Under.costar S).obj (B' i)) ≅
      Discrete.functor B' ⋙ CategoryTheory.Under.costar S :=
    Discrete.natIso (fun _ => Iso.refl _)
  let freeA : Cofan (fun i => (CategoryTheory.Under.costar S).obj (A' i)) :=
    (Cocone.precompose dA.hom).obj
      ((CategoryTheory.Under.costar S).mapCocone cofanA)
  let freeB : Cofan (fun i => (CategoryTheory.Under.costar S).obj (B' i)) :=
    (Cocone.precompose dB.hom).obj
      ((CategoryTheory.Under.costar S).mapCocone cofanB)
  let hFreeA : IsColimit freeA := by
    exact (IsColimit.precomposeHomEquiv dA _).symm
      (isColimitOfPreserves (CategoryTheory.Under.costar S) hA)
  let hFreeB : IsColimit freeB := by
    exact (IsColimit.precomposeHomEquiv dB _).symm
      (isColimitOfPreserves (CategoryTheory.Under.costar S) hB)
  let eA : freeA.pt ≅ c.cofan₁.pt :=
    hFreeA.coconePointUniqueUpToIso c.isColimit₁
  let eB : freeB.pt ≅ c.cofan₂.pt :=
    hFreeB.coconePointUniqueUpToIso c.isColimit₂
  have heA (i : c.ι) : freeA.inj i ≫ eA.hom = c.cofan₁.inj i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      hFreeA c.isColimit₁ (Discrete.mk i)
  have heB (i : c.ι) : freeB.inj i ≫ eB.hom = c.cofan₂.inj i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      hFreeB c.isColimit₂ (Discrete.mk i)
  have hfreeA (i : c.ι) : freeA.inj i =
      (CategoryTheory.Under.costar S).map (cofanA.inj i) := by
    simp [freeA, dA, Cofan.inj, Cocone.precompose_obj_ι,
      Functor.mapCocone_ι_app]
  have hfreeB (i : c.ι) : freeB.inj i =
      (CategoryTheory.Under.costar S).map (cofanB.inj i) := by
    simp [freeB, dB, Cofan.inj, Cocone.precompose_obj_ι,
      Functor.mapCocone_ι_app]
  let m : cofanA.pt ⟶ cofanB.pt := hA.desc
    (Cofan.mk cofanB.pt (fun i => g (c.π i) ≫ cofanB.inj i))
  have hm (i : c.ι) : cofanA.inj i ≫ m =
      g (c.π i) ≫ cofanB.inj i := hA.fac _ (Discrete.mk i)
  have hmap : (CategoryTheory.Under.costar S).map m ≫ eB.hom = eA.hom ≫ c.m := by
    apply Cofan.IsColimit.hom_ext hFreeA
    intro i
    calc
      freeA.inj i ≫ ((CategoryTheory.Under.costar S).map m ≫ eB.hom) =
          ((CategoryTheory.Under.costar S).map (cofanA.inj i) ≫
            (CategoryTheory.Under.costar S).map m) ≫ eB.hom := by
              rw [hfreeA, Category.assoc]
      _ = (CategoryTheory.Under.costar S).map (cofanA.inj i ≫ m) ≫
          eB.hom := by rw [Functor.map_comp]
      _ = (CategoryTheory.Under.costar S).map
          (g (c.π i) ≫ cofanB.inj i) ≫ eB.hom := by rw [hm]
      _ = ((CategoryTheory.Under.costar S).map (g (c.π i)) ≫
          (CategoryTheory.Under.costar S).map (cofanB.inj i)) ≫
            eB.hom := by rw [Functor.map_comp]
      _ = (CategoryTheory.Under.costar S).map (g (c.π i)) ≫
          (freeB.inj i ≫ eB.hom) := by rw [hfreeB, Category.assoc]
      _ = (CategoryTheory.Under.costar S).map (g (c.π i)) ≫
          c.cofan₂.inj i := by rw [heB]
      _ = c.cofan₁.inj i ≫ c.m := (c.hm i).symm
      _ = (freeA.inj i ≫ eA.hom) ≫ c.m := by rw [heA]
      _ = freeA.inj i ≫ (eA.hom ≫ c.m) := Category.assoc _ _ _
  have sqFree : IsPushout (eA.hom ≫ c.g₁) ((CategoryTheory.Under.costar S).map m)
      f (eB.hom ≫ c.g₂) := by
    refine c.isPushout.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← cancel_mono eB.hom]
    calc
      (c.m ≫ eB.inv) ≫ eB.hom = c.m := by simp
      _ = (eA.inv ≫ eA.hom) ≫ c.m := by simp
      _ = eA.inv ≫ (eA.hom ≫ c.m) := Category.assoc _ _ _
      _ = eA.inv ≫ ((CategoryTheory.Under.costar S).map m ≫ eB.hom) := by
        rw [hmap]
      _ = (eA.inv ≫ (CategoryTheory.Under.costar S).map m) ≫ eB.hom :=
        (Category.assoc _ _ _).symm
  let a : cofanA.pt ⟶ X.right :=
    (CategoryTheory.Under.costarAdjForget S).homEquiv cofanA.pt X (eA.hom ≫ c.g₁)
  let b : cofanB.pt ⟶ Y.right :=
    (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Y (eB.hom ≫ c.g₂)
  have sqBase : IsPushout a m f.right b := by
    have hcomm : a ≫ f.right = m ≫ b := by
      have hw := congrArg
        (fun k => (CategoryTheory.Under.costarAdjForget S).homEquiv cofanA.pt Y k)
        sqFree.w
      rw [(CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right,
        (CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_left] at hw
      exact hw
    refine { w := hcomm, isColimit' := ⟨?_⟩ }
    refine PushoutCocone.IsColimit.mk hcomm ?desc ?facLeft ?facRight ?uniq
    · intro s
      let Z : CategoryTheory.Under S := CategoryTheory.Under.mk (X.hom ≫ s.inl)
      let p : X ⟶ Z := CategoryTheory.Under.homMk s.inl rfl
      let q : (CategoryTheory.Under.costar S).obj cofanB.pt ⟶ Z :=
        ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z).symm s.inr
      have w : (eA.hom ≫ c.g₁) ≫ p =
          (CategoryTheory.Under.costar S).map m ≫ q := by
        apply ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanA.pt Z).injective
        rw [(CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right,
          (CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_left]
        have hp : (CategoryTheory.Under.forget S).map p = s.inl := rfl
        have hq : (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z q =
            s.inr := Equiv.apply_symm_apply _ _
        rw [hp, hq]
        exact s.condition
      exact (sqFree.desc p q w).right
    · intro s
      let Z : CategoryTheory.Under S := CategoryTheory.Under.mk (X.hom ≫ s.inl)
      let p : X ⟶ Z := CategoryTheory.Under.homMk s.inl rfl
      let q : (CategoryTheory.Under.costar S).obj cofanB.pt ⟶ Z :=
        ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z).symm s.inr
      have w : (eA.hom ≫ c.g₁) ≫ p =
          (CategoryTheory.Under.costar S).map m ≫ q := by
        apply ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanA.pt Z).injective
        rw [(CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right,
          (CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_left]
        have hp : (CategoryTheory.Under.forget S).map p = s.inl := rfl
        have hq : (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z q =
            s.inr := Equiv.apply_symm_apply _ _
        rw [hp, hq]
        exact s.condition
      have hw : f.right ≫ (sqFree.desc p q w).right = p.right :=
        congrArg CategoryTheory.Under.Hom.right (sqFree.inl_desc p q w)
      change f.right ≫ (sqFree.desc p q w).right = s.inl
      exact hw.trans rfl
    · intro s
      let Z : CategoryTheory.Under S := CategoryTheory.Under.mk (X.hom ≫ s.inl)
      let p : X ⟶ Z := CategoryTheory.Under.homMk s.inl rfl
      let q : (CategoryTheory.Under.costar S).obj cofanB.pt ⟶ Z :=
        ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z).symm s.inr
      have w : (eA.hom ≫ c.g₁) ≫ p =
          (CategoryTheory.Under.costar S).map m ≫ q := by
        apply ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanA.pt Z).injective
        rw [(CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right,
          (CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_left]
        have hp : (CategoryTheory.Under.forget S).map p = s.inl := rfl
        have hq : (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z q =
            s.inr := Equiv.apply_symm_apply _ _
        rw [hp, hq]
        exact s.condition
      have hw := congrArg
        (fun k => (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z k)
        (sqFree.inr_desc p q w)
      rw [(CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right] at hw
      have hq : (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z q =
          s.inr := Equiv.apply_symm_apply _ _
      have hd : (CategoryTheory.Under.forget S).map (sqFree.desc p q w) =
          (sqFree.desc p q w).right := rfl
      rw [hq, hd] at hw
      exact hw
    · intro s z hzLeft hzRight
      let Z : CategoryTheory.Under S := CategoryTheory.Under.mk (X.hom ≫ s.inl)
      let p : X ⟶ Z := CategoryTheory.Under.homMk s.inl rfl
      let q : (CategoryTheory.Under.costar S).obj cofanB.pt ⟶ Z :=
        ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z).symm s.inr
      have w : (eA.hom ≫ c.g₁) ≫ p =
          (CategoryTheory.Under.costar S).map m ≫ q := by
        apply ((CategoryTheory.Under.costarAdjForget S).homEquiv cofanA.pt Z).injective
        rw [(CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right,
          (CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_left]
        have hp : (CategoryTheory.Under.forget S).map p = s.inl := rfl
        have hq : (CategoryTheory.Under.costarAdjForget S).homEquiv cofanB.pt Z q =
            s.inr := Equiv.apply_symm_apply _ _
        rw [hp, hq]
        exact s.condition
      let z' : Y ⟶ Z := CategoryTheory.Under.homMk z (by
        dsimp [Z]
        rw [← CategoryTheory.Under.w f, Category.assoc, hzLeft])
      have hz' : z' = sqFree.desc p q w := by
        apply sqFree.hom_ext
        · apply CategoryTheory.Under.UnderMorphism.ext
          simpa [z', p] using hzLeft
        · have hzq : (eB.hom ≫ c.g₂) ≫ z' = q := by
            let b' : cofanB.pt ⟶
                (CategoryTheory.Under.forget S).obj Y := b
            have hOrig : ((CategoryTheory.Under.costarAdjForget S).homEquiv
                cofanB.pt Y).symm b' = eB.hom ≫ c.g₂ :=
              Equiv.symm_apply_apply _ _
            rw [← hOrig]
            rw [← (CategoryTheory.Under.costarAdjForget S).homEquiv_naturality_right_symm
              b' z']
            have hzMap : b' ≫ (CategoryTheory.Under.forget S).map z' =
                s.inr := by
              change b ≫ z = s.inr
              exact hzRight
            rw [hzMap]
          exact hzq.trans (sqFree.inr_desc p q w).symm
      exact congrArg CategoryTheory.Under.Hom.right hz'
  exact
    { ι := c.ι
      π := c.π
      cofan₁ := cofanA
      cofan₂ := cofanB
      isColimit₁ := hA
      isColimit₂ := hB
      m := m
      hm := hm
      g₁ := a
      g₂ := b
      isPushout := sqBase }

private noncomputable def forgetRelativeCellComplexUnderCostar
    {C : Type u} [Category.{v} C]
    [HasBinaryCoproducts C] [HasCoproducts.{w} C]
    (I : MorphismProperty C) (κ : Cardinal.{w})
    [OrderBot κ.ord.ToType]
    (S : C) {X Y : CategoryTheory.Under S} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => (I.underCostar S).homFamily) f) :
    RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => I.homFamily) f.right := by
  let _ : PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.Under.forget S) :=
    inferInstance
  let _ : PreservesWellOrderContinuousOfShape κ.ord.ToType
      (CategoryTheory.Under.forget S) :=
    { preservesColimitsOfShape := fun j hj => by
        let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
        let _ : IsFiltered (Set.Iio j) := inferInstance
        infer_instance }
  let _ : PreservesColimitsOfShape κ.ord.ToType (CategoryTheory.Under.forget S) := by
    infer_instance
  exact
    { toTransfiniteCompositionOfShape :=
        c.toTransfiniteCompositionOfShape.map (CategoryTheory.Under.forget S)
      attachCells := fun j hj => by
        let a := c.attachCells j hj
        let h (p : (I.underCostar S).toSet) :=
          strictMapPreimage_exists I (CategoryTheory.Under.costar S) (by
            simpa only [MorphismProperty.toSet, Set.mem_ofPred_eq,
              MorphismProperty.underCostar] using p.2)
        let q (p : (I.underCostar S).toSet) : I.toSet := (h p).choose
        let e (p : (I.underCostar S).toSet) :
            CategoryTheory.Arrow.mk p.1.hom ≅
              CategoryTheory.Arrow.mk ((CategoryTheory.Under.costar S).map (I.homFamily (q p))) :=
          Classical.choice (h p).choose_spec
        let a' := a.reindexCellTypes
          (fun p : I.toSet => (CategoryTheory.Under.costar S).map (I.homFamily p)) q e
        simpa [CategoryTheory.TransfiniteCompositionOfShape.map] using
          forgetAttachCellsUnderCostar S I.homFamily a' }

private theorem preservesColimit_underCostar
    {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [HasBinaryCoproducts C] (S : C)
    (hI : I.IsCardinalForSmallObjectArgument κ)
    {A B X Y : CategoryTheory.Under S} (i : A ⟶ B) (hi : (I.underCostar S) i)
    (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => (I.underCostar S).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  let _ : HasCoproducts.{w} C := hI.hasCoproducts
  have hi' : (I.strictMap (CategoryTheory.Under.costar S)) i := by
    simpa [MorphismProperty.underCostar] using hi
  let h := strictMapPreimage_exists I (CategoryTheory.Under.costar S) hi'
  let q : I.toSet := h.choose
  let e : CategoryTheory.Arrow.mk i ≅
      CategoryTheory.Arrow.mk
        ((CategoryTheory.Under.costar S).map q.1.hom) :=
    Classical.choice h.choose_spec
  let hfb := forgetRelativeCellComplexUnderCostar I κ S hf
  have hBase : PreservesColimit (hf.F ⋙ CategoryTheory.Under.forget S)
      (coyoneda.obj (Opposite.op q.1.left)) := by
    simpa [hfb, forgetRelativeCellComplexUnderCostar,
      CategoryTheory.TransfiniteCompositionOfShape.map] using
      hI.preservesColimit q.1.hom q.2 f.right hfb
  let _ : PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.Under.forget S) :=
    inferInstance
  let _ : IsFiltered κ.ord.ToType := inferInstance
  let _ : PreservesColimitsOfShape κ.ord.ToType (CategoryTheory.Under.forget S) :=
    inferInstance
  let _ : PreservesColimit hf.F (CategoryTheory.Under.forget S) := inferInstance
  let _ : PreservesColimit (hf.F ⋙ CategoryTheory.Under.forget S)
      (coyoneda.obj (Opposite.op q.1.left)) := hBase
  let _ : PreservesColimit hf.F
      (CategoryTheory.Under.forget S ⋙ coyoneda.obj (Opposite.op q.1.left)) :=
    inferInstance
  let hCostar : PreservesColimit hf.F
      (coyoneda.obj
        (Opposite.op ((CategoryTheory.Under.costar S).obj q.1.left))) :=
    preservesColimit_of_natIso hf.F (costarCoyonedaIso S q.1.left)
  let _ : PreservesColimit hf.F
      (coyoneda.obj
        (Opposite.op ((CategoryTheory.Under.costar S).obj q.1.left))) := hCostar
  let eLeft : A ≅ (CategoryTheory.Under.costar S).obj q.1.left :=
    CategoryTheory.Arrow.leftFunc.mapIso e
  exact preservesColimit_of_natIso hf.F (coyoneda.mapIso eLeft.op)

/-- A fixed small-object cardinal is preserved by strict costar images. -/
theorem underCostar
    {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [HasBinaryCoproducts C] (S : C)
    [HasCoproducts.{w} (CategoryTheory.Under S)]
    (hI : I.IsCardinalForSmallObjectArgument κ) :
    (I.underCostar S).IsCardinalForSmallObjectArgument κ := by
  let _ : LocallySmall.{w} C := hI.locallySmall
  let _ : HasPushouts C := hI.hasPushouts
  let _ : HasPushouts (CategoryTheory.Under S) := inferInstance
  let _ : HasIterationOfShape κ.ord.ToType C := hI.hasIterationOfShape
  let _ : HasIterationOfShape κ.ord.ToType (CategoryTheory.Under S) := by
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
  exact
    { isSmall := by
        change (I.strictMap (CategoryTheory.Under.costar S)).IsSmall.{w}
        exact hI.isSmall.strictMap (CategoryTheory.Under.costar S)
      locallySmall := locallySmall_of_faithful (CategoryTheory.Under.forget S)
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := preservesColimit_underCostar I κ S hI }

end CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument

namespace HomotopicalAlgebra.CofibrantGenerationData

/-- Explicit cofibrant-generation data transfers to an Under category at
the same regular cardinal. -/
noncomputable def under
    {C : Type u} [Category.{v} C] [ModelCategory C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (G : CofibrantGenerationData C κ) (S : C)
    [HasCoproducts.{w} (CategoryTheory.Under S)] :
    CofibrantGenerationData (CategoryTheory.Under S) κ := by
  let _ : HasCoproducts.{w} C := G.I_smallObject.hasCoproducts
  let _ : HasBinaryCoproducts C := inferInstance
  exact
    { I := G.I.underCostar S
      J := G.J.underCostar S
      I_smallObject :=
        CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.underCostar
          G.I κ S G.I_smallObject
      J_smallObject :=
        CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.underCostar
          G.J κ S G.J_smallObject
      I_rlp := by
        calc
          (G.I.underCostar S).rlp =
              G.I.rlp.inverseImage (CategoryTheory.Under.forget S) :=
            MorphismProperty.underCostar_rlp G.I S
          _ = (trivialFibrations C).inverseImage (CategoryTheory.Under.forget S) :=
            congrArg (fun P : MorphismProperty C =>
              P.inverseImage (CategoryTheory.Under.forget S)) G.I_rlp
          _ = (trivialFibrations C).under :=
            (MorphismProperty.under_eq_inverseImage
              (trivialFibrations C) S).symm
          _ = trivialFibrations (CategoryTheory.Under S) :=
            (trivialFibrations_under_eq S).symm
      J_rlp := by
        calc
          (G.J.underCostar S).rlp =
              G.J.rlp.inverseImage (CategoryTheory.Under.forget S) :=
            MorphismProperty.underCostar_rlp G.J S
          _ = (fibrations C).inverseImage (CategoryTheory.Under.forget S) :=
            congrArg (fun P : MorphismProperty C =>
              P.inverseImage (CategoryTheory.Under.forget S)) G.J_rlp
          _ = (fibrations C).under :=
            (MorphismProperty.under_eq_inverseImage (fibrations C) S).symm
          _ = fibrations (CategoryTheory.Under S) :=
            (fibrations_under_def S).symm }

end HomotopicalAlgebra.CofibrantGenerationData
