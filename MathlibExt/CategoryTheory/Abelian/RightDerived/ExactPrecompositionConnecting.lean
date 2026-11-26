/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.ExactPrecompositionZero
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedCoefficientConnecting
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Precomposition

/-!
# Right-derived connecting maps under homology-preserving source change

Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
The image by `U` of a short exact sequence is short exact. The directional
comparisons `R^n(U ⋙ L) → U ⋙ R^nL` commute with the associated
connecting morphisms and form a morphism of cohomological delta-functors.
This uses no injective-preservation hypothesis on `U` or exactness
hypothesis on `L`.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
  {A : Type uA} [Category.{vA} A] [Abelian A]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
  (L : D ⥤ A) [L.Additive]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- For abelian `C,D` and additive homology-preserving `U : C → D`,
the image `U(X₁) → U(X₂) → U(X₃)` of a short exact sequence
`S : X₁ → X₂ → X₃` is short exact. -/
theorem rightDerivedPrecompShortExact (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map U).ShortExact := by
  let : PreservesFiniteLimits U := preservesFiniteLimits_of_preservesHomology U
  let : PreservesFiniteColimits U := preservesFiniteColimits_of_preservesHomology U
  exact hS.map_of_exact U

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
For a short exact `S : X₁ → X₂ → X₃`, the directional comparisons
satisfy `δ_(U⋙L),n ≫ η_(n+1),X₁ = η_n,X₃ ≫ δ_L,n(U(S))`,
where the connecting maps run from degree `n` at `X₃` to degree `n+1`
at `X₁`. -/
@[reassoc]
theorem rightDerivedPrecompHomOfPreservesHomology_connecting
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    ((U ⋙ L).rightDerivedConnecting n).app ⟨S, hS⟩ ≫
        (rightDerivedPrecompHomOfPreservesHomology U L (n + 1)).app S.X₁ =
      (rightDerivedPrecompHomOfPreservesHomology U L n).app S.X₃ ≫
        (L.rightDerivedConnecting n).app ⟨S.map U, rightDerivedPrecompShortExact U S hS⟩ := by
  let H := RightDerived.HorseshoeData.ofEndpoints S hS
    (injectiveResolution S.X₁) (injectiveResolution S.X₃)
  let M := U.mapHomologicalComplex (ComplexShape.up ℕ)
  let P := H.diagram.map M
  let ι₁ : (CochainComplex.single₀ D).obj (U.obj S.X₁) ⟶
      (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj H.res₁.cocomplex :=
    mapCochainCoaugmentation U H.res₁.ι
  let ι₂ : (CochainComplex.single₀ D).obj (U.obj S.X₂) ⟶
      (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj H.res₂.cocomplex :=
    mapCochainCoaugmentation U H.res₂.ι
  let ι₃ : (CochainComplex.single₀ D).obj (U.obj S.X₃) ⟶
      (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj H.res₃.cocomplex :=
    mapCochainCoaugmentation U H.res₃.ι
  let : QuasiIso ι₁ := mapCochainCoaugmentation_quasiIso U H.res₁.ι
  let : QuasiIso ι₂ := mapCochainCoaugmentation_quasiIso U H.res₂.ι
  let : QuasiIso ι₃ := mapCochainCoaugmentation_quasiIso U H.res₃.ι
  have hf : ι₁.f 0 ≫ P.f.f 0 = (S.map U).f ≫ ι₂.f 0 := by
    change (mapCochainCoaugmentation U H.res₁.ι).f 0 ≫ U.map (H.φf.f 0) =
      U.map S.f ≫ (mapCochainCoaugmentation U H.res₂.ι).f 0
    let p₁ : S.X₁ ⟶ H.res₁.cocomplex.X 0 := H.res₁.ι.f 0
    let p₂ : S.X₂ ⟶ H.res₂.cocomplex.X 0 := H.res₂.ι.f 0
    let a : H.res₁.cocomplex.X 0 ⟶ H.res₂.cocomplex.X 0 := H.φf.f 0
    have hLift : p₁ ≫ a = S.f ≫ p₂ := H.lift_f
    have h₁ := mapCochainCoaugmentation_f_zero U H.res₁.ι
    have h₂ := mapCochainCoaugmentation_f_zero U H.res₂.ι
    exact (congrArg₂ (fun z w => z ≫ w) h₁ rfl).trans
      ((U.map_comp p₁ a).symm.trans
        ((congrArg U.map hLift).trans
          ((U.map_comp S.f p₂).trans
            (congrArg (fun z => U.map S.f ≫ z) h₂.symm))))
  have hg : ι₂.f 0 ≫ P.g.f 0 = (S.map U).g ≫ ι₃.f 0 := by
    change (mapCochainCoaugmentation U H.res₂.ι).f 0 ≫ U.map (H.φg.f 0) =
      U.map S.g ≫ (mapCochainCoaugmentation U H.res₃.ι).f 0
    let p₂ : S.X₂ ⟶ H.res₂.cocomplex.X 0 := H.res₂.ι.f 0
    let p₃ : S.X₃ ⟶ H.res₃.cocomplex.X 0 := H.res₃.ι.f 0
    let a : H.res₂.cocomplex.X 0 ⟶ H.res₃.cocomplex.X 0 := H.φg.f 0
    have hLift : p₂ ≫ a = S.g ≫ p₃ := H.lift_g
    have h₂ := mapCochainCoaugmentation_f_zero U H.res₂.ι
    have h₃ := mapCochainCoaugmentation_f_zero U H.res₃.ι
    exact (congrArg₂ (fun z w => z ≫ w) h₂ rfl).trans
      ((U.map_comp p₂ a).symm.trans
        ((congrArg U.map hLift).trans
          ((U.map_comp S.g p₃).trans
            (congrArg (fun z => U.map S.g ≫ z) h₃.symm))))
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)
  let Q := P.map (L.mapHomologicalComplex (ComplexShape.up ℕ))
  have hQ : Q.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    have h := (((H.split i).map U).map L).shortExact
    change ((HomologicalComplex.eval A (ComplexShape.up ℕ) i).mapShortComplex.obj Q).ShortExact
    exact h
  let hLow := H.mapped_shortExact (U ⋙ L)
  let φ : H.mapped (U ⋙ L) ⟶ Q := H.diagram.mapNatTrans χ.inv
  let dLow := hLow.δ n (n + 1) rfl
  let dHigh := hQ.δ n (n + 1) rfl
  let b₁ := HomologicalComplex.homologyMap (χ.inv.app H.res₁.cocomplex) (n + 1)
  let b₃ := HomologicalComplex.homologyMap (χ.inv.app H.res₃.cocomplex) n
  let q₁ := L.augmentedResolutionToRightDerivedHom
    ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj H.res₁.cocomplex) ι₁ (n + 1)
  let q₃ := L.augmentedResolutionToRightDerivedHom
    ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj H.res₃.cocomplex) ι₃ n
  let a₁ := H.res₁.isoRightDerivedObj (U ⋙ L) (n + 1)
  let a₃ := H.res₃.isoRightDerivedObj (U ⋙ L) n
  let dF := ((U ⋙ L).rightDerivedConnecting n).app ⟨S, hS⟩
  let dL := (L.rightDerivedConnecting n).app
    ⟨S.map U, rightDerivedPrecompShortExact U S hS⟩
  have hMiddle : dLow ≫ b₁ = b₃ ≫ dHigh :=
    HomologicalComplex.HomologySequence.δ_naturality φ hLow hQ n (n + 1) rfl
  have hLast : dHigh ≫ q₁ = q₃ ≫ dL := by
    let κ₁ : (CochainComplex.single₀ D).obj (S.map U).X₁ ⟶ P.X₁ := ι₁
    let : QuasiIso κ₁ := by
      change QuasiIso (mapCochainCoaugmentation U H.res₁.ι)
      exact mapCochainCoaugmentation_quasiIso U H.res₁.ι
    let κ₂ : (CochainComplex.single₀ D).obj (S.map U).X₂ ⟶ P.X₂ := ι₂
    let : QuasiIso κ₂ := by
      change QuasiIso (mapCochainCoaugmentation U H.res₂.ι)
      exact mapCochainCoaugmentation_quasiIso U H.res₂.ι
    let κ₃ : (CochainComplex.single₀ D).obj (S.map U).X₃ ⟶ P.X₃ := ι₃
    let : QuasiIso κ₃ := by
      change QuasiIso (mapCochainCoaugmentation U H.res₃.ι)
      exact mapCochainCoaugmentation_quasiIso U H.res₃.ι
    have h := L.augmentedResolutionToRightDerivedHom_connecting
      (S.map U) (rightDerivedPrecompShortExact U S hS) P κ₁ κ₂ κ₃ hf hg hQ n
    dsimp only [q₁, q₃, dHigh, dL, P, M, Q, κ₁, κ₃,
      RightDerived.HorseshoeData.diagram, ShortComplex.map_X₁, ShortComplex.map_X₃] at h ⊢
    exact h
  have hNative : dF = a₃.hom ≫ dLow ≫ a₁.inv := by
    rfl
  have hFirst : dF ≫ a₁.hom = a₃.hom ≫ dLow :=
    (Iso.eq_comp_inv a₁).mp
      (hNative.trans (Category.assoc a₃.hom dLow a₁.inv).symm)
  have hγ₁ : (rightDerivedPrecompHomOfPreservesHomology U L (n + 1)).app S.X₁ =
      a₁.hom ≫ b₁ ≫ q₁ := by
    rw [rightDerivedPrecompHomOfPreservesHomology_app U L (n + 1) H.res₁]
    unfold rightDerivedPrecompHomWithResolution
    dsimp only [a₁, b₁, q₁, ι₁, χ]
  have hγ₃ : (rightDerivedPrecompHomOfPreservesHomology U L n).app S.X₃ =
      a₃.hom ≫ b₃ ≫ q₃ := by
    rw [rightDerivedPrecompHomOfPreservesHomology_app U L n H.res₃]
    unfold rightDerivedPrecompHomWithResolution
    dsimp only [a₃, b₃, q₃, ι₃, χ]
  have s₁ : CommSq a₃.hom dF dLow a₁.hom := ⟨hFirst.symm⟩
  have s₂ : CommSq b₃ dLow dHigh b₁ := ⟨hMiddle.symm⟩
  have s₃ : CommSq q₃ dHigh dL q₁ := ⟨hLast.symm⟩
  rw [hγ₁, hγ₃]
  exact (s₁.horiz_comp (s₂.horiz_comp s₃)).w.symm

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
The degree comparisons `R^n(U ⋙ L) → U ⋙ R^nL` and their connecting-map
squares form a morphism from the delta-functor of `U ⋙ L` to the
right-derived delta-functor of `L` precomposed with `U`. -/
def rightDerivedPrecompDeltaHomOfPreservesHomology :
    (U ⋙ L).rightDerivedDeltaFunctor ⟶
      CohomologicalDeltaFunctor.precompose U (rightDerivedPrecompShortExact U)
        L.rightDerivedDeltaFunctor :=
  CohomologicalDeltaFunctor.homMk C A
    (fun n => rightDerivedPrecompHomOfPreservesHomology U L n)
    (fun n S => rightDerivedPrecompHomOfPreservesHomology_connecting U L n S.obj S.property)

@[simp]
theorem rightDerivedPrecompDeltaHomOfPreservesHomology_app (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (rightDerivedPrecompDeltaHomOfPreservesHomology U L) n =
      rightDerivedPrecompHomOfPreservesHomology U L n := rfl

end CategoryTheory.Functor
