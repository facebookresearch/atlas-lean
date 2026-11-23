/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.CartesianClosed

/-!
# Tests for compactly generated Cartesian closedness
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace MathlibExtTest.CompactlyGenerated.CartesianClosedTests

private noncomputable def binaryKificationIso
    (X Y : CompactlyGenerated.{u, v}) :
    TopCat.toCompactlyGenerated.obj
        (TopCat.of (↑X × ↑Y)) ≅ X ⊗ Y := by
  let PF : ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp :
      ((TopCat.piFan (fun j ↦
        CompactlyGenerated.compactlyGeneratedToTop.obj (PF j))).pt :
          Type v) ≃ₜ ↑X × ↑Y :=
    { toEquiv :=
        { toFun := fun g =>
            (show X from g (ULift.up WalkingPair.left),
              show Y from g (ULift.up WalkingPair.right))
          invFun := fun p j => match j with
            | ⟨WalkingPair.left⟩ => p.1
            | ⟨WalkingPair.right⟩ => p.2
          left_inv := fun g => by
            funext j
            rcases j with ⟨_ | _⟩ <;> rfl
          right_inv := fun p => by rcases p with ⟨x, y⟩; rfl }
      continuous_toFun :=
        (continuous_apply (ULift.up WalkingPair.left)).prodMk
          (continuous_apply (ULift.up WalkingPair.right))
      continuous_invFun := by
        apply continuous_pi
        intro j
        rcases j with ⟨_ | _⟩
        · exact continuous_fst
        · exact continuous_snd }
  let eTensor : (∏ᶜ PF) ≅ X ⊗ Y := by
    let c : Fan PF := Fan.mk (X ⊗ Y) (fun j => match j with
      | ⟨WalkingPair.left⟩ => CartesianMonoidalCategory.fst X Y
      | ⟨WalkingPair.right⟩ => CartesianMonoidalCategory.snd X Y)
    let hc : IsLimit c := by
      refine
        { lift := fun s => CartesianMonoidalCategory.lift
            (s.π.app ⟨ULift.up WalkingPair.left⟩)
            (s.π.app ⟨ULift.up WalkingPair.right⟩)
          fac := ?_
          uniq := ?_ }
      · rintro s ⟨⟨j⟩⟩
        cases j
        · exact CartesianMonoidalCategory.lift_fst _ _
        · exact CartesianMonoidalCategory.lift_snd _ _
      · intro s m hm
        apply CartesianMonoidalCategory.hom_ext
        · exact (hm ⟨ULift.up WalkingPair.left⟩).trans
            (CartesianMonoidalCategory.lift_fst _ _).symm
        · exact (hm ⟨ULift.up WalkingPair.right⟩).trans
            (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (limit.isLimit _).conePointUniqueUpToIso hc
  exact TopCat.toCompactlyGenerated.mapIso
      (TopCat.isoOfHomeo hp.symm) ≪≫
    (CompactlyGenerated.piIsoPi PF).symm ≪≫ eTensor

private theorem continuousToKifiedMax
    {S : Type max u v} {T : Type v}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} S]
    {h : S → T} (hh : Continuous h) :
    @Continuous S T inferInstance
      (TopologicalSpace.compactlyGenerated.{u} T) h := by
  apply continuous_from_uCompactlyGeneratedSpace.{u, max u v, v}
    (tY := TopologicalSpace.compactlyGenerated.{u} T) h
  intro K g
  rw [TopologicalSpace.compactlyGenerated]
  let q : @ContinuousMap K T _ tT :=
    ⟨h ∘ g, hh.comp g.continuous⟩
  let ev :
      (Σ (i : (L : CompHaus.{u}) × @ContinuousMap L T _ tT), i.fst) → T :=
    fun ⟨⟨_, i⟩, x⟩ => i x
  change @Continuous K T inferInstance
    (TopologicalSpace.coinduced ev inferInstance)
    (fun x => ev ⟨⟨K, q⟩, x⟩)
  have hmk : Continuous (fun x : K =>
      (⟨⟨K, q⟩, x⟩ :
        Σ (i : (L : CompHaus.{u}) × @ContinuousMap L T _ tT), i.fst)) :=
    continuous_sigmaMk
      (ι := (L : CompHaus.{u}) × @ContinuousMap L T _ tT)
      (σ := fun i => i.fst) (i := ⟨K, q⟩)
  let _ : TopologicalSpace T :=
    TopologicalSpace.coinduced ev inferInstance
  have hev : Continuous ev := continuous_coinduced_rng
  exact hev.comp hmk

private theorem continuousToKified
    {S T : Type v}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} S]
    {h : S → T} (hh : Continuous h) :
    @Continuous S T inferInstance
      (TopologicalSpace.compactlyGenerated.{u} T) h := by
  apply continuous_from_uCompactlyGeneratedSpace.{u, v, v}
    (tY := TopologicalSpace.compactlyGenerated.{u} T) h
  intro K g
  rw [TopologicalSpace.compactlyGenerated]
  let q : @ContinuousMap K T _ tT :=
    ⟨h ∘ g, hh.comp g.continuous⟩
  let ev :
      (Σ (i : (L : CompHaus.{u}) × @ContinuousMap L T _ tT), i.fst) → T :=
    fun ⟨⟨_, i⟩, x⟩ => i x
  change @Continuous K T inferInstance
    (TopologicalSpace.coinduced ev inferInstance)
    (fun x => ev ⟨⟨K, q⟩, x⟩)
  have hmk : Continuous (fun x : K =>
      (⟨⟨K, q⟩, x⟩ :
        Σ (i : (L : CompHaus.{u}) × @ContinuousMap L T _ tT), i.fst)) :=
    continuous_sigmaMk
      (ι := (L : CompHaus.{u}) × @ContinuousMap L T _ tT)
      (σ := fun i => i.fst) (i := ⟨K, q⟩)
  let _ : TopologicalSpace T :=
    TopologicalSpace.coinduced ev inferInstance
  have hev : Continuous ev := continuous_coinduced_rng
  exact hev.comp hmk

private noncomputable def rawCurry
    {X Y Z : CompactlyGenerated.{u, v}}
    (f : X ⊗ Y ⟶ Z) : C(Y, C(X, Z)) := by
  let e := binaryKificationIso X Y
  let ψRaw : Y → C(X, Z) := fun y => by
    let hRaw : X →
        (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
          ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) :=
      fun x => (x, y)
    have hRawContinuous : Continuous hRaw :=
      continuous_id.prodMk continuous_const
    have hKified : @Continuous X
        (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
          ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) inferInstance
        (TopologicalSpace.compactlyGenerated.{u} _) hRaw :=
      continuousToKified hRawContinuous
    let hToPair : X ⟶ TopCat.toCompactlyGenerated.obj
        (TopCat.of (↑X × ↑Y)) :=
      ConcreteCategory.ofHom ⟨hRaw, by
        have ht : (TopCat.toCompactlyGenerated.obj
            (TopCat.of (↑X × ↑Y))).toTop.str =
            TopologicalSpace.compactlyGenerated.{u}
              (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
                ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) := by
          change TopologicalSpace.generatedBy
            CompactlyGenerated.compactHausProbes (Y := ↑X × ↑Y) = _
          exact
            TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
        rw [ht]
        exact hKified⟩
    exact ConcreteCategory.hom (hToPair ≫ e.hom ≫ f)
  have hψRaw : Continuous ψRaw := by
    apply continuous_from_uCompactlyGeneratedSpace.{u, v, v} ψRaw
    intro K g
    let _ : UCompactlyGeneratedSpace.{u} (K × X) :=
      uCompactlyGeneratedSpace_prod_of_locallyCompact_left
        (A := K) (B := X)
    let hRaw : K × X →
        (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
          ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) :=
      fun p => (p.2, g p.1)
    have hRawContinuous : Continuous hRaw :=
      continuous_snd.prodMk (g.continuous.comp continuous_fst)
    have hKified : @Continuous (K × X)
        (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
          ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) inferInstance
        (TopologicalSpace.compactlyGenerated.{u} _) hRaw :=
      continuousToKifiedMax hRawContinuous
    have hKified' : @Continuous (K × X)
        (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
          ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) inferInstance
        (TopCat.toCompactlyGenerated.obj
          (TopCat.of (↑X × ↑Y))).toTop.str hRaw := by
      have ht : (TopCat.toCompactlyGenerated.obj
          (TopCat.of (↑X × ↑Y))).toTop.str =
          TopologicalSpace.compactlyGenerated.{u}
            (↑(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
              ↑(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) := by
        change TopologicalSpace.generatedBy
          CompactlyGenerated.compactHausProbes (Y := ↑X × ↑Y) = _
        exact
          TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
      rw [ht]
      exact hKified
    have hNative : Continuous (fun p : K × X => e.hom (hRaw p)) :=
      (ConcreteCategory.hom e.hom).continuous.comp hKified'
    have hUncurry : Continuous (fun p : K × X =>
        f (e.hom (hRaw p))) :=
      (ConcreteCategory.hom f).continuous.comp hNative
    let φ : K → C(X, Z) := fun k =>
      ⟨fun x => f (e.hom (x, g k)),
        hUncurry.comp (continuous_const.prodMk continuous_id)⟩
    have hφ : Continuous φ :=
      ContinuousMap.continuous_of_continuous_uncurry φ (by
        change Continuous (fun p : K × X => f (e.hom (p.2, g p.1)))
        exact hUncurry)
    exact hφ.congr (fun k => by
      apply ContinuousMap.ext
      intro x
      dsimp only [φ, Function.comp_apply]
      dsimp [ψRaw]
      rfl)
  exact ⟨ψRaw, hψRaw⟩

private theorem curry_apply
    {X Y Z : CompactlyGenerated.{u, v}}
    (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    (CompactlyGenerated.internalHomToCompactOpen X Z
      (CompactlyGenerated.curry f y)) x =
        f ((binaryKificationIso X Y).hom (x, y)) := by
  let raw : CompactlyGenerated.compactlyGeneratedToTop.obj Y ⟶
      TopCat.of C(X, Z) := TopCat.ofHom (rawCurry f)
  have hCurry : CompactlyGenerated.curry f =
      CompactlyGenerated.adj.homEquiv Y (TopCat.of C(X, Z)) raw := by
    unfold CompactlyGenerated.curry
    unfold CompactlyGenerated.internalHomAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have hLanding :
      CompactlyGenerated.compactlyGeneratedToTop.map
          (CompactlyGenerated.curry f) ≫
        CompactlyGenerated.internalHomToCompactOpen X Z = raw := by
    rw [hCurry]
    change (CompactlyGenerated.adj.homEquiv Y
      (TopCat.of C(X, Z))).symm
        ((CompactlyGenerated.adj.homEquiv Y
          (TopCat.of C(X, Z))) raw) = raw
    exact (CompactlyGenerated.adj.homEquiv Y
      (TopCat.of C(X, Z))).symm_apply_apply raw
  have hy := ConcreteCategory.congr_hom hLanding y
  have hx := congrArg (fun q : C(X, Z) => q x) hy
  change (CompactlyGenerated.internalHomToCompactOpen X Z
      (CompactlyGenerated.curry f y)) x = raw y x at hx
  exact hx.trans (by rfl)

private theorem uncurry_apply
    {X Y Z : CompactlyGenerated.{u, v}}
    (g : Y ⟶ (CompactlyGenerated.internalHom X).obj Z)
    (y : Y) (x : X) :
    CompactlyGenerated.uncurry g
        ((binaryKificationIso X Y).hom (x, y)) =
      (CompactlyGenerated.internalHomToCompactOpen X Z (g y)) x := by
  have hInv : CompactlyGenerated.curry
      (CompactlyGenerated.uncurry g) = g :=
    ((CompactlyGenerated.internalHomAdjunction X).homEquiv Y Z).apply_symm_apply g
  calc
    CompactlyGenerated.uncurry g
          ((binaryKificationIso X Y).hom (x, y)) =
        (CompactlyGenerated.internalHomToCompactOpen X Z
          (CompactlyGenerated.curry (CompactlyGenerated.uncurry g) y)) x :=
      (curry_apply (CompactlyGenerated.uncurry g) y x).symm
    _ = (CompactlyGenerated.internalHomToCompactOpen X Z (g y)) x := by
      rw [hInv]

section PublicSurface

#check CompactlyGenerated.internalHom
#check CompactlyGenerated.internalHomToCompactOpen
#check CompactlyGenerated.internalHomToCompactOpen_apply
#check CompactlyGenerated.internalHomAdjunction
#check CompactlyGenerated.eval
#check CompactlyGenerated.curry
#check CompactlyGenerated.uncurry
#check CompactlyGenerated.instMonoidalClosed

end PublicSurface

section CarrierAndComparison

variable (X Y : CompactlyGenerated.{u, v})

example : (CompactlyGenerated.internalHom X).obj Y =
    TopCat.toCompactlyGenerated.obj (TopCat.of C(X, Y)) := rfl

example :
    CompactlyGenerated.compactlyGeneratedToTop.obj
        ((CompactlyGenerated.internalHom X).obj Y) ⟶
      TopCat.of C(X, Y) :=
  CompactlyGenerated.internalHomToCompactOpen X Y

example (f : (CompactlyGenerated.internalHom X).obj Y) :
    CompactlyGenerated.internalHomToCompactOpen X Y f = f :=
  CompactlyGenerated.internalHomToCompactOpen_apply X Y f

end CarrierAndComparison

section SemanticPointFormulas

variable {X Y Z : CompactlyGenerated.{u, v}}

example (x : X) (h : (CompactlyGenerated.internalHom X).obj Z) :
    CompactlyGenerated.eval X Z
        ((binaryKificationIso X
          ((CompactlyGenerated.internalHom X).obj Z)).hom (x, h)) =
      (CompactlyGenerated.internalHomToCompactOpen X Z h) x := by
  have hEval : CompactlyGenerated.uncurry
      (𝟙 ((CompactlyGenerated.internalHom X).obj Z)) =
        CompactlyGenerated.eval X Z := by
    simpa [CompactlyGenerated.uncurry, CompactlyGenerated.eval] using
      (CompactlyGenerated.internalHomAdjunction X).homEquiv_counit
        (g := 𝟙 ((CompactlyGenerated.internalHom X).obj Z))
  rw [← hEval]
  simpa using uncurry_apply
    (𝟙 ((CompactlyGenerated.internalHom X).obj Z)) h x

example (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    (CompactlyGenerated.internalHomToCompactOpen X Z
      (CompactlyGenerated.curry f y)) x =
        f ((binaryKificationIso X Y).hom (x, y)) := by
  exact curry_apply f y x

example (g : Y ⟶ (CompactlyGenerated.internalHom X).obj Z)
    (y : Y) (x : X) :
    CompactlyGenerated.uncurry g
        ((binaryKificationIso X Y).hom (x, y)) =
      (CompactlyGenerated.internalHomToCompactOpen X Z (g y)) x := by
  exact uncurry_apply g y x

end SemanticPointFormulas

section AdjunctionDerivedOperations

variable {X Y Y' Z Z' : CompactlyGenerated.{u, v}}

example : CompactlyGenerated.eval X Z =
    (CompactlyGenerated.internalHomAdjunction X).counit.app Z := rfl

example (f : X ⊗ Y ⟶ Z) : CompactlyGenerated.curry f =
    (CompactlyGenerated.internalHomAdjunction X).homEquiv Y Z f := rfl

example (g : Y ⟶ (CompactlyGenerated.internalHom X).obj Z) :
    CompactlyGenerated.uncurry g =
      ((CompactlyGenerated.internalHomAdjunction X).homEquiv Y Z).symm g := rfl

example (f : X ⊗ Y ⟶ Z) :
    CompactlyGenerated.uncurry (CompactlyGenerated.curry f) = f :=
  ((CompactlyGenerated.internalHomAdjunction X).homEquiv Y Z).symm_apply_apply f

example (g : Y ⟶ (CompactlyGenerated.internalHom X).obj Z) :
    CompactlyGenerated.curry (CompactlyGenerated.uncurry g) = g :=
  ((CompactlyGenerated.internalHomAdjunction X).homEquiv Y Z).apply_symm_apply g

example (a : Y' ⟶ Y) (f : X ⊗ Y ⟶ Z) :
    CompactlyGenerated.curry ((X ◁ a) ≫ f) =
      a ≫ CompactlyGenerated.curry f :=
  (CompactlyGenerated.internalHomAdjunction X).homEquiv_naturality_left a f

example (f : X ⊗ Y ⟶ Z) (b : Z ⟶ Z') :
    CompactlyGenerated.curry (f ≫ b) =
      CompactlyGenerated.curry f ≫
        (CompactlyGenerated.internalHom X).map b :=
  (CompactlyGenerated.internalHomAdjunction X).homEquiv_naturality_right f b

example (a : Y' ⟶ Y)
    (g : Y ⟶ (CompactlyGenerated.internalHom X).obj Z) :
    CompactlyGenerated.uncurry (a ≫ g) =
      (X ◁ a) ≫ CompactlyGenerated.uncurry g :=
  (CompactlyGenerated.internalHomAdjunction X).homEquiv_naturality_left_symm a g

example (g : Y ⟶ (CompactlyGenerated.internalHom X).obj Z)
    (b : Z ⟶ Z') :
    CompactlyGenerated.uncurry
        (g ≫ (CompactlyGenerated.internalHom X).map b) =
      CompactlyGenerated.uncurry g ≫ b :=
  (CompactlyGenerated.internalHomAdjunction X).homEquiv_naturality_right_symm g b

example (Y : CompactlyGenerated.{u, v}) :
    (tensorLeft X).map
          ((CompactlyGenerated.internalHomAdjunction X).unit.app Y) ≫
        (CompactlyGenerated.internalHomAdjunction X).counit.app
          ((tensorLeft X).obj Y) = 𝟙 _ :=
  (CompactlyGenerated.internalHomAdjunction X).left_triangle_components Y

example (Z : CompactlyGenerated.{u, v}) :
    (CompactlyGenerated.internalHomAdjunction X).unit.app
          ((CompactlyGenerated.internalHom X).obj Z) ≫
        (CompactlyGenerated.internalHom X).map
          ((CompactlyGenerated.internalHomAdjunction X).counit.app Z) = 𝟙 _ :=
  (CompactlyGenerated.internalHomAdjunction X).right_triangle_components Z

end AdjunctionDerivedOperations

section UniversesAndInstances

example : MonoidalClosed CompactlyGenerated.{0, 0} := inferInstance
example : MonoidalClosed CompactlyGenerated.{1, 1} := inferInstance
example : MonoidalClosed CompactlyGenerated.{0, 1} := inferInstance
example : MonoidalClosed CompactlyGenerated.{1, 0} := inferInstance

example (X : CompactlyGenerated.{u, v}) : Closed X := inferInstance

example :
    (inferInstance : MonoidalClosed CompactlyGenerated.{u, v}) =
      CompactlyGenerated.instMonoidalClosed := rfl

end UniversesAndInstances

section PrivacyAndTrust

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.binaryKificationIso

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.evalPair0

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.unit_apply

#print axioms CompactlyGenerated.internalHom
#print axioms CompactlyGenerated.internalHomToCompactOpen
#print axioms CompactlyGenerated.internalHomToCompactOpen_apply
#print axioms CompactlyGenerated.internalHomAdjunction
#print axioms CompactlyGenerated.eval
#print axioms CompactlyGenerated.curry
#print axioms CompactlyGenerated.uncurry
#print axioms CompactlyGenerated.instMonoidalClosed

end PrivacyAndTrust

end MathlibExtTest.CompactlyGenerated.CartesianClosedTests
