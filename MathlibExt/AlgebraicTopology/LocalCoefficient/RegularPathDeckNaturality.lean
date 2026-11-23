/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatHomology
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularRelativeComparison
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Conj
public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoidPath
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Logic.Small.Defs

/-!
# Deck naturality of the original regular path coefficients

Inverse precomposition acts on the same regular path functor. Its chain
map agrees with the actual native deck map under the established path
coordinate comparison. Forward coefficient transport remains postcomposition.
-/

noncomputable section
public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

private local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

private local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I => inferInstanceAs (HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ))

namespace CategoryTheory

/-- Inverse precomposition on the original free integral path functor. -/
def regularPathInversePrecomposition {C : Type u} [Groupoid.{v} C]
    (y : C) (a : End y) :
    regularPathModuleCoefficientFunctor y ⟶ regularPathModuleCoefficientFunctor y where
  app z := ModuleCat.ofHom (FreeAbelianGroup.map (fun γ : y ⟶ z => (a⁻¹).asHom ≫ γ)).toIntLinearMap
  naturality {z z'} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    refine FreeAbelianGroup.lift_ext _ _ ?_
    intro γ
    change FreeAbelianGroup.map (fun δ : y ⟶ z' => (a⁻¹).asHom ≫ δ)
        ((regularPathModuleCoefficientFunctor y).map f (FreeAbelianGroup.of γ)) =
      (regularPathModuleCoefficientFunctor y).map f
        (FreeAbelianGroup.map (fun δ : y ⟶ z => (a⁻¹).asHom ≫ δ) (FreeAbelianGroup.of γ))
    rw [regularPathModuleCoefficientFunctor_map_of, FreeAbelianGroup.map_of_apply,
      FreeAbelianGroup.map_of_apply, regularPathModuleCoefficientFunctor_map_of]
    exact congrArg FreeAbelianGroup.of (Category.assoc _ _ _).symm

/-- Every original path is acted on by the inverse original endomorphism. -/
theorem regularPathInversePrecomposition_of {C : Type u} [Groupoid.{v} C]
    (y : C) (a : End y) (z : C) (γ : y ⟶ z) :
    (regularPathInversePrecomposition y a).app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of ((a⁻¹).asHom ≫ γ) := by
  exact FreeAbelianGroup.map_of_apply γ

/-- The identity endomorphism acts by the identity natural transformation. -/
theorem regularPathInversePrecomposition_one {C : Type u} [Groupoid.{v} C] (y : C) :
    regularPathInversePrecomposition y (1 : End y) = 𝟙 _ := by
  apply NatTrans.ext
  funext z
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  exact (regularPathInversePrecomposition_of y 1 z γ).trans
    (congrArg FreeAbelianGroup.of (by simp))

/-- Its multiplication law is the actual LEFT action law, with no
commutativity assumption on the endomorphism group. -/
theorem regularPathInversePrecomposition_mul {C : Type u} [Groupoid.{v} C]
    (y : C) (a b : End y) :
    regularPathInversePrecomposition y (a*b) =
      regularPathInversePrecomposition y b ≫ regularPathInversePrecomposition y a := by
  apply NatTrans.ext
  funext z
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  have h1 := regularPathInversePrecomposition_of y (a*b) z γ
  have h2 := regularPathInversePrecomposition_of y b z γ
  have h3 := regularPathInversePrecomposition_of y a z ((b⁻¹).asHom ≫ γ)
  change _ = (regularPathInversePrecomposition y a).app z
    ((regularPathInversePrecomposition y b).app z (FreeAbelianGroup.of γ))
  exact h1.trans ((congrArg FreeAbelianGroup.of (by
    simp only [mul_inv_rev, End.mul_asHom, Category.assoc])).trans
      ((congrArg ((regularPathInversePrecomposition y a).app z) h2).trans h3).symm)

end CategoryTheory

namespace SSet.KanComplex

/-- Compose the actual lifted simplex with the original native deck map. -/
def nativeCoverDeckedSimplexLift {Y : SSet.{u}} (y : Y _⦋0⦌)
    (a : End (SSet.FundamentalGroupoid.mk y)) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ Y)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y // L ≫ nativeCoverProjection Y y = σ}) :
    {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y // L ≫ nativeCoverProjection Y y = σ} :=
  ⟨L.val ≫ nativeCoverDeckMap a,
    (Category.assoc L.val (nativeCoverDeckMap a) (nativeCoverProjection Y y)).trans
      ((congrArg (fun f => L.val ≫ f) (nativeCoverDeckMap_projection a)).trans L.property)⟩

/-- The computed decked lift retains the whole original lifted simplex map. -/
theorem nativeCoverDeckedSimplexLift_val {Y : SSet.{u}} (y : Y _⦋0⦌)
    (a : End (SSet.FundamentalGroupoid.mk y)) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ Y)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y // L ≫ nativeCoverProjection Y y = σ}) :
    (nativeCoverDeckedSimplexLift y a σ L).val = L.val ≫ nativeCoverDeckMap a := by
  rfl

/-- The actual lifted simplex changes its original first-path coordinate by
inverse precomposition under the native deck map. -/
theorem nativeCoverSimplexFiberPathEquiv_deck {Y : SSet.{u}} [SSet.KanComplex Y]
    (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ Y)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y // L ≫ nativeCoverProjection Y y = σ}) :
    nativeCoverSimplexFiberPathEquiv σ (nativeCoverDeckedSimplexLift y a σ L) =
      (a⁻¹).asHom ≫ nativeCoverSimplexFiberPathEquiv σ L := by
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let z : Y _⦋0⦌ := SSet.yonedaEquiv (X := Y) (n := ⦋0⦌) (α ≫ σ)
  let V₀ : Type u := {v : (nativeCover Y y) _⦋0⦌ //
    (nativeCoverProjection Y y).app (Opposite.op ⦋0⦌) v = z}
  let v : V₀ := nativeCoverSimplexFiberVertexEquiv (X := Y) (x := y) σ L
  let aπ : π 1 Y y := (piOneMulEquivFundamentalGroupoidEnd y).symm a
  have ha : piOneMulEquivFundamentalGroupoidEnd y aπ = a :=
    (piOneMulEquivFundamentalGroupoidEnd y).apply_symm_apply a
  let : MulAction (π 1 Y y) V₀ := nativeCoverPiOneVertexFiberAction (X := Y) y z
  have hVertex : nativeCoverSimplexFiberVertexEquiv (X := Y) (x := y) σ
      (nativeCoverDeckedSimplexLift y a σ L) = (aπ • v : V₀) := by
    apply Subtype.ext
    change SSet.yonedaEquiv (α ≫ (L.val ≫ nativeCoverDeckMap a)) =
      (nativeCoverDeckMap (piOneMulEquivFundamentalGroupoidEnd y aπ)).app _ v.val
    have hAssoc := congrArg (SSet.yonedaEquiv (X := nativeCover Y y) (n := ⦋0⦌))
      (Category.assoc α L.val (nativeCoverDeckMap a)).symm
    exact hAssoc.trans ((SSet.yonedaEquiv_comp (α ≫ L.val) (nativeCoverDeckMap a)).trans
      (congrArg (fun b => (nativeCoverDeckMap b).app _ v.val) ha.symm))
  change nativeCoverVertexPathEquiv z (nativeCoverSimplexFiberVertexEquiv σ
    (nativeCoverDeckedSimplexLift y a σ L)) = (a⁻¹).asHom ≫ nativeCoverVertexPathEquiv z v
  exact (congrArg (nativeCoverVertexPathEquiv z) hVertex).trans
    ((nativeCoverVertexPathEquiv_smul (X := Y) y z aπ v).trans
      (congrArg (fun b : End (SSet.FundamentalGroupoid.mk y) =>
        (b⁻¹).asHom ≫ nativeCoverVertexPathEquiv z v) ha))

/-- Every native simplex generator keeps its actual simplex and path; the
deck action changes only that path by inverse precomposition. -/
theorem nativeCoverSimplexPathGeneratorsEquiv_deck {Y : SSet.{u}} [SSet.KanComplex Y]
    (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) (n : ℕ)
    (σ : (Δ[n] : SSet.{u}) ⟶ Y)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk
      (SSet.yonedaEquiv ((SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ))) :
    nativeCoverSimplexPathGeneratorsEquiv Y y n ⟨σ, (a⁻¹).asHom ≫ γ⟩ =
      (nativeCoverDeckMap a).app (Opposite.op ⦋n⦌)
        (nativeCoverSimplexPathGeneratorsEquiv Y y n ⟨σ, γ⟩) := by
  let φ := nativeCoverSimplexFiberPathEquiv (X := Y) (x := y) σ
  let L := φ.symm γ
  let La := nativeCoverDeckedSimplexLift y a σ L
  have hPath : φ La = (a⁻¹).asHom ≫ γ :=
    (nativeCoverSimplexFiberPathEquiv_deck y a σ L).trans
      (congrArg (fun δ => (a⁻¹).asHom ≫ δ) (φ.apply_symm_apply γ))
  have hLift : φ.symm ((a⁻¹).asHom ≫ γ) = La :=
    (congrArg φ.symm hPath.symm).trans (φ.symm_apply_apply La)
  have h1 := nativeCoverSimplexPathGeneratorsEquiv_apply Y y n σ ((a⁻¹).asHom ≫ γ)
  have h2 := nativeCoverSimplexPathGeneratorsEquiv_apply Y y n σ γ
  have h3 : SSet.yonedaEquiv (φ.symm ((a⁻¹).asHom ≫ γ)).val =
      (nativeCoverDeckMap a).app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv L.val) :=
    (congrArg (fun T => SSet.yonedaEquiv T.val) hLift).trans
      (SSet.yonedaEquiv_comp L.val (nativeCoverDeckMap a))
  exact h1.trans (h3.trans
    (congrArg (fun s => (nativeCoverDeckMap a).app (Opposite.op ⦋n⦌) s) h2.symm))

/-- The actual deck map of the literal pulled cover fixes its first
projection and acts by the same original deck map on its second projection. -/
def nativeRegularPullbackDeckMap {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    pullback f (nativeCoverProjection Y y) ⟶ pullback f (nativeCoverProjection Y y) := by
  let p := nativeCoverProjection Y y
  let r := pullback.snd f p
  let q := pullback.fst f p
  let d := nativeCoverDeckMap a
  have hw : q ≫ f = (r ≫ d) ≫ p :=
    (pullback.condition (f := f) (g := p)).trans
      ((congrArg (fun t => r ≫ t) (nativeCoverDeckMap_projection a).symm).trans
        (Category.assoc r d p).symm)
  exact pullback.lift q (r ≫ d) hw

/-- The old-cover deck map retains the actual original first projection. -/
theorem nativeRegularPullbackDeckMap_fst {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    nativeRegularPullbackDeckMap f y a ≫ pullback.fst f (nativeCoverProjection Y y) =
      pullback.fst f (nativeCoverProjection Y y) := by
  exact pullback.lift_fst _ _ _

/-- The same old-cover deck map has the original native second projection. -/
theorem nativeRegularPullbackDeckMap_snd {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌)
    (a : End (SSet.FundamentalGroupoid.mk y)) :
    nativeRegularPullbackDeckMap f y a ≫ pullback.snd f (nativeCoverProjection Y y) =
      pullback.snd f (nativeCoverProjection Y y) ≫ nativeCoverDeckMap a := by
  exact pullback.lift_snd _ _ _

private def deckedPullbackSimplexLift {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌)
    (a : End (SSet.FundamentalGroupoid.mk y)) {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ}) :
    {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ} :=
  ⟨L.val ≫ nativeRegularPullbackDeckMap f y a,
    (Category.assoc _ _ _).trans
      ((congrArg (fun h => L.val ≫ h) (nativeRegularPullbackDeckMap_fst f y a)).trans L.property)⟩

private theorem pullbackSimplexPath_deck {X Y : SSet.{u}} [SSet.KanComplex Y]
    (f : X ⟶ Y) (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ}) :
    nativeCoverPullbackSimplexPathEquiv f y σ (deckedPullbackSimplexLift f y a σ L) =
      (a⁻¹).asHom ≫ nativeCoverPullbackSimplexPathEquiv f y σ L := by
  let r := pullback.snd f (nativeCoverProjection Y y)
  let T := nativeCoverPullbackSimplexFiberEquiv f y σ L
  let Ta := nativeCoverPullbackSimplexFiberEquiv f y σ
    (deckedPullbackSimplexLift f y a σ L)
  let Td := nativeCoverDeckedSimplexLift y a (σ ≫ f) T
  have hT : Ta = Td := by
    apply Subtype.ext
    change (L.val ≫ nativeRegularPullbackDeckMap f y a) ≫ r = T.val ≫ nativeCoverDeckMap a
    exact (Category.assoc _ _ _).trans
      (congrArg (fun h => L.val ≫ h) (nativeRegularPullbackDeckMap_snd f y a))
  change nativeCoverSimplexFiberPathEquiv (σ ≫ f) Ta =
    (a⁻¹).asHom ≫ nativeCoverSimplexFiberPathEquiv (σ ≫ f) T
  exact (congrArg (nativeCoverSimplexFiberPathEquiv (σ ≫ f)) hT).trans
    (nativeCoverSimplexFiberPathEquiv_deck y a (σ ≫ f) T)

/-- The original path generator of every pulled-cover simplex intertwines
inverse precomposition with the actual pulled deck map. -/
theorem nativeCoverPullbackSimplexPathGeneratorsEquiv_deck {X Y : SSet.{u}} [SSet.KanComplex Y]
    (f : X ⟶ Y) (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) (n : ℕ)
    (g : nativeCoverPullbackSimplexPathGenerators f y n) :
    nativeCoverPullbackSimplexPathGeneratorsEquiv f y n ⟨g.1, (a⁻¹).asHom ≫ g.2⟩ =
      (nativeRegularPullbackDeckMap f y a).app (Opposite.op ⦋n⦌)
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n g) := by
  let φ := nativeCoverPullbackSimplexPathEquiv f y g.1
  let L := φ.symm g.2
  let La := deckedPullbackSimplexLift f y a g.1 L
  have hPath : φ La = (a⁻¹).asHom ≫ g.2 :=
    (pullbackSimplexPath_deck f y a g.1 L).trans
      (congrArg (fun γ => (a⁻¹).asHom ≫ γ) (φ.apply_symm_apply g.2))
  have hLift : φ.symm ((a⁻¹).asHom ≫ g.2) = La :=
    (congrArg φ.symm hPath.symm).trans (φ.symm_apply_apply La)
  have h1 := nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f y n
    ⟨g.1, (a⁻¹).asHom ≫ g.2⟩
  have h2 := nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f y n g
  have h3 : SSet.yonedaEquiv (φ.symm ((a⁻¹).asHom ≫ g.2)).val =
      (nativeRegularPullbackDeckMap f y a).app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv L.val) :=
    (congrArg (fun T => SSet.yonedaEquiv T.val) hLift).trans
      (SSet.yonedaEquiv_comp L.val (nativeRegularPullbackDeckMap f y a))
  exact h1.trans (h3.trans
    (congrArg (fun s => (nativeRegularPullbackDeckMap f y a).app (Opposite.op ⦋n⦌) s) h2.symm))

private theorem originalNativeIndex_deck (Y : SSet.{u}) [SSet.KanComplex Y]
    (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) (n : ℕ) (s : Y _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ ((fundamentalGroupoidNerveUnit Y).app _ s).left) :
    nativeCoverSimplexPathGeneratorsEquiv Y y n
        (regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
          (SSet.FundamentalGroupoid.mk y) n ⟨s, (a⁻¹).asHom ≫ γ⟩) =
      (nativeCoverDeckMap a).app (Opposite.op ⦋n⦌)
        (nativeCoverSimplexPathGeneratorsEquiv Y y n
          (regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
            (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩)) := by
  let σ : (Δ[n] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm s
  let κ := regularLocalCoefficientFirstObject_eq s
  let δ := γ ≫ eqToHom κ
  let G := nativeCoverSimplexPathGeneratorsEquiv Y y n
  let I := 𝟭 (SSet.FundamentalGroupoid Y)
  have h1 : regularLocalCoefficientPathIndexEquiv I (SSet.FundamentalGroupoid.mk y) n
      ⟨s, (a⁻¹).asHom ≫ γ⟩ = ⟨σ, (a⁻¹).asHom ≫ δ⟩ :=
    (regularLocalCoefficientPathIndexEquiv_apply I _ n s ((a⁻¹).asHom ≫ γ)).trans
      (congrArg (fun h => (⟨σ, h⟩ : nativeCoverSimplexPathGenerators Y y n))
        (Category.assoc (a⁻¹).asHom γ (eqToHom κ)))
  have h2 : regularLocalCoefficientPathIndexEquiv I (SSet.FundamentalGroupoid.mk y) n
      ⟨s, γ⟩ = ⟨σ, δ⟩ := regularLocalCoefficientPathIndexEquiv_apply I _ n s γ
  exact (congrArg G h1).trans
    ((nativeCoverSimplexPathGeneratorsEquiv_deck y a n σ δ).trans
      (congrArg (fun g => (nativeCoverDeckMap a).app _ (G g)) h2.symm))

private theorem originalPullbackIndex_deck {X Y : SSet.{u}} [SSet.KanComplex Y]
    (f : X ⟶ Y) (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) (n : ℕ)
    (s : X _⦋n⦌)
    (γ : SSet.FundamentalGroupoid.mk y ⟶ (SSet.mapFundamentalGroupoid f).obj
      ((fundamentalGroupoidNerveUnit X).app _ s).left) :
    nativeCoverPullbackSimplexPathGeneratorsEquiv f y n
        (regularLocalCoefficientPullbackPathIndexEquiv f y n
          (regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
            (SSet.FundamentalGroupoid.mk y) n ⟨s, (a⁻¹).asHom ≫ γ⟩)) =
      (nativeRegularPullbackDeckMap f y a).app (Opposite.op ⦋n⦌)
        (nativeCoverPullbackSimplexPathGeneratorsEquiv f y n
          (regularLocalCoefficientPullbackPathIndexEquiv f y n
            (regularLocalCoefficientPathIndexEquiv (SSet.mapFundamentalGroupoid f)
              (SSet.FundamentalGroupoid.mk y) n ⟨s, γ⟩))) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid f
  let b : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
  let σ : (Δ[n] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm s
  let κ := congrArg F.obj (regularLocalCoefficientFirstObject_eq s)
  let χ := regularLocalCoefficientPullbackEndpoint_eq f σ
  let δ := (γ ≫ eqToHom κ) ≫ eqToHom χ
  let I := regularLocalCoefficientPathIndexEquiv F b n
  let J := regularLocalCoefficientPullbackPathIndexEquiv f y n
  let G := nativeCoverPullbackSimplexPathGeneratorsEquiv f y n
  let pA : regularLocalCoefficientPathGenerators F b n :=
    ⟨σ, ((a⁻¹).asHom ≫ γ) ≫ eqToHom κ⟩
  let p₀ : regularLocalCoefficientPathGenerators F b n := ⟨σ, γ ≫ eqToHom κ⟩
  have h1 : J (I ⟨s, (a⁻¹).asHom ≫ γ⟩) = ⟨σ, (a⁻¹).asHom ≫ δ⟩ := by
    have hI : I ⟨s, (a⁻¹).asHom ≫ γ⟩ = pA :=
      regularLocalCoefficientPathIndexEquiv_apply F b n s ((a⁻¹).asHom ≫ γ)
    have hJ : J pA = ⟨σ, (((a⁻¹).asHom ≫ γ) ≫ eqToHom κ) ≫ eqToHom χ⟩ :=
      regularLocalCoefficientPullbackPathIndexEquiv_apply f y n pA
    have hPath : (((a⁻¹).asHom ≫ γ) ≫ eqToHom κ) ≫ eqToHom χ =
        (a⁻¹).asHom ≫ δ :=
      (congrArg (fun h => h ≫ eqToHom χ)
        (Category.assoc (a⁻¹).asHom γ (eqToHom κ))).trans
          (Category.assoc (a⁻¹).asHom (γ ≫ eqToHom κ) (eqToHom χ))
    exact (congrArg J hI).trans
      (hJ.trans (congrArg
        (fun h => (⟨σ, h⟩ : nativeCoverPullbackSimplexPathGenerators f y n)) hPath))
  have h2 : J (I ⟨s, γ⟩) = ⟨σ, δ⟩ := by
    have hI : I ⟨s, γ⟩ = p₀ := regularLocalCoefficientPathIndexEquiv_apply F b n s γ
    have hJ : J p₀ = ⟨σ, δ⟩ := regularLocalCoefficientPullbackPathIndexEquiv_apply f y n p₀
    exact (congrArg J hI).trans hJ
  exact (congrArg G h1).trans
    ((nativeCoverPullbackSimplexPathGeneratorsEquiv_deck f y a n ⟨σ, δ⟩).trans
      (congrArg (fun g => (nativeRegularPullbackDeckMap f y a).app _ (G g)) h2.symm))

/-- The existing native chain comparison intertwines the original regular
coefficient action with the SAME deck map in every degree. -/
theorem originalNativeRegularCoverChainIso_deck (Y : SSet.{u}) [SSet.KanComplex Y]
    (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) :
    SSet.localCoefficientChainMap (CategoryTheory.regularPathInversePrecomposition
        (SSet.FundamentalGroupoid.mk y) a) ≫
      (originalNativeRegularCoefficientCoverChainIso Y y).hom =
        (originalNativeRegularCoefficientCoverChainIso Y y).hom ≫
          SSet.chainComplexMap (nativeCoverDeckMap a) (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let L := CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
  let α := CategoryTheory.regularPathInversePrecomposition (SSet.FundamentalGroupoid.mk y) a
  let e := originalNativeRegularCoefficientCoverChainIso Y y
  let W := nativeCover Y y
  let d := SSet.chainComplexMap (nativeCoverDeckMap a) (ModuleCat.of ℤ (ULift.{u} ℤ))
  apply HomologicalComplex.hom_ext
  intro n
  apply CategoryTheory.CategoryHomology.nervePullbackCoefficient_hom_ext
      (fundamentalGroupoidNerveUnit Y) L
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  let γa := (a⁻¹).asHom ≫ γ
  let v := SSet.localCoefficientι L s (FreeAbelianGroup.of γ)
  let va := SSet.localCoefficientι L s (FreeAbelianGroup.of γa)
  let G := nativeCoverSimplexPathGeneratorsEquiv Y y n
  let I := regularLocalCoefficientPathIndexEquiv (𝟭 (SSet.FundamentalGroupoid Y))
    (SSet.FundamentalGroupoid.mk y) n
  have hα : (SSet.localCoefficientChainMap α).f n v = va :=
    (ConcreteCategory.congr_hom
      (SSet.localCoefficientι_map α s) (FreeAbelianGroup.of γ)).trans
        (congrArg (SSet.localCoefficientι L s)
          (CategoryTheory.regularPathInversePrecomposition_of _ a _ γ))
  have ha : e.hom.f n va = W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      (G (I ⟨s, γa⟩)) (ULift.up (1 : ℤ)) := by
    let ι := CategoryTheory.CategoryHomology.nervePullbackCoefficientι
      (fundamentalGroupoidNerveUnit Y) L s
    have hUnit : ι ((1 : ℤ) • FreeAbelianGroup.of γa) = va :=
      (congrArg ι (one_zsmul (FreeAbelianGroup.of γa))).trans
        (show ι (FreeAbelianGroup.of γa) = va from rfl)
    have hBasis : e.hom.f n (ι ((1 : ℤ) • FreeAbelianGroup.of γa)) =
        W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
          (G (I ⟨s, γa⟩)) (ULift.up (1 : ℤ)) :=
      originalNativeRegularCoefficientCoverChainIso_hom_ι_basis Y y n s γa 1
    exact (congrArg (fun z => e.hom.f n z) hUnit.symm).trans hBasis
  have h0 : e.hom.f n v = W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      (G (I ⟨s, γ⟩)) (ULift.up (1 : ℤ)) := by
    let ι := CategoryTheory.CategoryHomology.nervePullbackCoefficientι
      (fundamentalGroupoidNerveUnit Y) L s
    have hUnit : ι ((1 : ℤ) • FreeAbelianGroup.of γ) = v :=
      (congrArg ι (one_zsmul (FreeAbelianGroup.of γ))).trans
        (show ι (FreeAbelianGroup.of γ) = v from rfl)
    have hBasis : e.hom.f n (ι ((1 : ℤ) • FreeAbelianGroup.of γ)) =
        W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
          (G (I ⟨s, γ⟩)) (ULift.up (1 : ℤ)) :=
      originalNativeRegularCoefficientCoverChainIso_hom_ι_basis Y y n s γ 1
    exact (congrArg (fun z => e.hom.f n z) hUnit.symm).trans hBasis
  have hd : d.f n (W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      (G (I ⟨s, γ⟩)) (ULift.up (1 : ℤ))) =
    W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      ((nativeCoverDeckMap a).app _ (G (I ⟨s, γ⟩))) (ULift.up (1 : ℤ)) :=
    ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f (X := W) (Y := W)
      (f := nativeCoverDeckMap a) (R := ModuleCat.of ℤ (ULift.{u} ℤ)) (n := n)
      (show W _⦋n⦌ from G (I ⟨s, γ⟩))) (ULift.up (1 : ℤ))
  change e.hom.f n ((SSet.localCoefficientChainMap α).f n v) = d.f n (e.hom.f n v)
  exact (congrArg (e.hom.f n) hα).trans
    (ha.trans ((congrArg (fun g => W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ)) g
      (ULift.up (1 : ℤ))) (originalNativeIndex_deck Y y a n s γ)).trans
        ((congrArg (d.f n) h0).trans hd).symm))

/-- The established pulled-cover comparison has the same action square on
all original simplex/path coefficients. -/
theorem regularLocalCoefficientPullbackCoverChainIso_deck {X Y : SSet.{u}} [SSet.KanComplex Y]
    (f : X ⟶ Y) (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) :
    SSet.localCoefficientChainMap (Functor.whiskerLeft (SSet.mapFundamentalGroupoid f)
        (CategoryTheory.regularPathInversePrecomposition (SSet.FundamentalGroupoid.mk y) a)) ≫
      (regularLocalCoefficientPullbackCoverChainIso f y).hom =
        (regularLocalCoefficientPullbackCoverChainIso f y).hom ≫
          SSet.chainComplexMap (nativeRegularPullbackDeckMap f y a)
              (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let F := SSet.mapFundamentalGroupoid f
  let L := F ⋙ CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
  let α := Functor.whiskerLeft F (CategoryTheory.regularPathInversePrecomposition
    (SSet.FundamentalGroupoid.mk y) a)
  let e := regularLocalCoefficientPullbackCoverChainIso f y
  let W := pullback f (nativeCoverProjection Y y)
  let d := SSet.chainComplexMap (nativeRegularPullbackDeckMap f y a) (ModuleCat.of ℤ (ULift.{u} ℤ))
  apply HomologicalComplex.hom_ext
  intro n
  apply CategoryTheory.CategoryHomology.nervePullbackCoefficient_hom_ext
      (fundamentalGroupoidNerveUnit X) L
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  let γa := (a⁻¹).asHom ≫ γ
  let v := SSet.localCoefficientι L s (FreeAbelianGroup.of γ)
  let va := SSet.localCoefficientι L s (FreeAbelianGroup.of γa)
  let G := nativeCoverPullbackSimplexPathGeneratorsEquiv f y n
  let I := regularLocalCoefficientPathIndexEquiv F (SSet.FundamentalGroupoid.mk y) n
  let J := regularLocalCoefficientPullbackPathIndexEquiv f y n
  have hα : (SSet.localCoefficientChainMap α).f n v = va :=
    (ConcreteCategory.congr_hom (SSet.localCoefficientι_map α s) (FreeAbelianGroup.of γ)).trans
      (congrArg (SSet.localCoefficientι L s)
        (CategoryTheory.regularPathInversePrecomposition_of _ a _ γ))
  have ha : e.hom.f n va = W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      (G (J (I ⟨s, γa⟩))) (ULift.up (1 : ℤ)) := by
    let ι := CategoryTheory.CategoryHomology.nervePullbackCoefficientι
      (fundamentalGroupoidNerveUnit X) L s
    have hUnit : ι ((1 : ℤ) • FreeAbelianGroup.of γa) = va :=
      (congrArg ι (one_zsmul (FreeAbelianGroup.of γa))).trans
        (show ι (FreeAbelianGroup.of γa) = va from rfl)
    have hBasis : e.hom.f n (ι ((1 : ℤ) • FreeAbelianGroup.of γa)) =
        W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
          (G (J (I ⟨s, γa⟩))) (ULift.up (1 : ℤ)) :=
      regularLocalCoefficientPullbackCoverChainIso_hom_ι_basis f y n s γa 1
    exact (congrArg (fun z => e.hom.f n z) hUnit.symm).trans hBasis
  have h0 : e.hom.f n v = W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      (G (J (I ⟨s, γ⟩))) (ULift.up (1 : ℤ)) := by
    let ι := CategoryTheory.CategoryHomology.nervePullbackCoefficientι
      (fundamentalGroupoidNerveUnit X) L s
    have hUnit : ι ((1 : ℤ) • FreeAbelianGroup.of γ) = v :=
      (congrArg ι (one_zsmul (FreeAbelianGroup.of γ))).trans
        (show ι (FreeAbelianGroup.of γ) = v from rfl)
    have hBasis : e.hom.f n (ι ((1 : ℤ) • FreeAbelianGroup.of γ)) =
        W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
          (G (J (I ⟨s, γ⟩))) (ULift.up (1 : ℤ)) :=
      regularLocalCoefficientPullbackCoverChainIso_hom_ι_basis f y n s γ 1
    exact (congrArg (fun z => e.hom.f n z) hUnit.symm).trans hBasis
  have hd : d.f n (W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      (G (J (I ⟨s, γ⟩))) (ULift.up (1 : ℤ))) =
    W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
      ((nativeRegularPullbackDeckMap f y a).app _ (G (J (I ⟨s, γ⟩)))) (ULift.up (1 : ℤ)) :=
    ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f (X := W) (Y := W)
      (f := nativeRegularPullbackDeckMap f y a) (R := ModuleCat.of ℤ (ULift.{u} ℤ)) (n := n)
      (show W _⦋n⦌ from G (J (I ⟨s, γ⟩)))) (ULift.up (1 : ℤ))
  change e.hom.f n ((SSet.localCoefficientChainMap α).f n v) = d.f n (e.hom.f n v)
  exact (congrArg (e.hom.f n) hα).trans
    (ha.trans ((congrArg (fun g => W.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ)) g
      (ULift.up (1 : ℤ))) (originalPullbackIndex_deck f y a n s γ)).trans
        ((congrArg (d.f n) h0).trans hd).symm))

end SSet.KanComplex

namespace TopCat

/-- The actual topological endomorphism represented by a native singular
endomorphism, with the existing derived basepoint cast. -/
def singularRegularEndHom (Y : TopCat.{u}) (y : Y) :
    End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) →*
      End (_root_.FundamentalGroupoid.mk y) :=
  (eqToIso (singularRegularBasepoint_eq Y y)).conj.toMonoidHom.comp
    ((singularFundamentalGroupoidFunctor Y).mapEnd
      (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)))

/-- The actual topological endomorphism includes only the existing basepoint cast. -/
theorem singularRegularEndHom_asHom (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    (singularRegularEndHom Y y a).asHom =
      (eqToIso (singularRegularBasepoint_eq Y y)).inv ≫
        (singularFundamentalGroupoidFunctor Y).map a.asHom ≫
          (eqToIso (singularRegularBasepoint_eq Y y)).hom := by
  rfl

/-- The original endomorphism homomorphism is the same established
singular fundamental-groupoid endomorphism equivalence on values. -/
theorem singularRegularEndHom_eq (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    singularRegularEndHom Y y a = singularFundamentalGroupoidEndMulEquiv Y y a := by
  apply End.ext
  rfl

/-- The computed singular path dictionary intertwines the original
inverse-precomposition actions, including the actual point cast. -/
theorem singularRegularPathEquiv_inverse_precomposition (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)))
    (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
    (γ : SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z) :
    singularRegularPathEquiv Y y z ((a⁻¹).asHom ≫ γ) =
      ((singularRegularEndHom Y y a)⁻¹).asHom ≫ singularRegularPathEquiv Y y z γ := by
  let F := singularFundamentalGroupoidFunctor Y
  let e := eqToIso (singularRegularBasepoint_eq Y y)
  have hInv : (singularRegularEndHom Y y a)⁻¹ = singularRegularEndHom Y y (a⁻¹) :=
    ((singularRegularEndHom Y y).map_inv a).symm
  rw [hInv, singularRegularEndHom_asHom, singularRegularPathEquiv_apply,
    singularRegularPathEquiv_apply]
  change e.inv ≫ F.map ((a⁻¹).asHom ≫ γ) =
    (e.inv ≫ F.map (a⁻¹).asHom ≫ e.hom) ≫ (e.inv ≫ F.map γ)
  simp only [F.map_comp, Category.assoc, e.hom_inv_id_assoc]

/-- The regular coefficient deck action on the original topological paths. -/
def originalRegularDeckCoefficient (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y) ⟶
      CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y) :=
  CategoryTheory.regularPathInversePrecomposition (_root_.FundamentalGroupoid.mk y)
    (singularRegularEndHom Y y a)

/-- Its characteristic formula is actual inverse precomposition, rather
than a separately transported module structure. -/
theorem originalRegularDeckCoefficient_of (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)))
    (z : _root_.FundamentalGroupoid Y) (γ : _root_.FundamentalGroupoid.mk y ⟶ z) :
    (originalRegularDeckCoefficient Y y a).app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (((singularRegularEndHom Y y a)⁻¹).asHom ≫ γ) :=
  CategoryTheory.regularPathInversePrecomposition_of _ _ _ _

/-- The existing singular coefficient comparison preserves this SAME
original deck action on every path. -/
theorem singularRegularCoefficientIso_inverse_precomposition (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    CategoryTheory.regularPathInversePrecomposition
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) a ≫
      (singularRegularCoefficientIso Y y).hom =
        (singularRegularCoefficientIso Y y).hom ≫
          LocalSystem.toSingularMap (originalRegularDeckCoefficient Y y a) := by
  apply NatTrans.ext
  funext z
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  have h1 := CategoryTheory.regularPathInversePrecomposition_of
    (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) a z γ
  have h2 := singularRegularCoefficientIso_hom_of Y y z ((a⁻¹).asHom ≫ γ)
  have h3 := singularRegularCoefficientIso_hom_of Y y z γ
  have h4 := originalRegularDeckCoefficient_of Y y a
    ((singularFundamentalGroupoidFunctor Y).obj z) (singularRegularPathEquiv Y y z γ)
  change (singularRegularCoefficientIso Y y).hom.app z
      ((CategoryTheory.regularPathInversePrecomposition _ a).app z (FreeAbelianGroup.of γ)) =
    (originalRegularDeckCoefficient Y y a).app _
      ((singularRegularCoefficientIso Y y).hom.app z (FreeAbelianGroup.of γ))
  exact (congrArg ((singularRegularCoefficientIso Y y).hom.app z) h1).trans
    (h2.trans ((congrArg FreeAbelianGroup.of
      (singularRegularPathEquiv_inverse_precomposition Y y a z γ)).trans
        ((congrArg ((originalRegularDeckCoefficient Y y a).app _) h3).trans h4).symm))

/-- Pulling back the existing coefficient comparison preserves the same
inverse-precomposition action on every original source path. -/
theorem singularRegularPullbackCoefficientIso_inverse_precomposition {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    Functor.whiskerLeft (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))
        (CategoryTheory.regularPathInversePrecomposition
          (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) a) ≫
      (singularRegularPullbackCoefficientIso f y).hom =
        (singularRegularPullbackCoefficientIso f y).hom ≫
          LocalSystem.toSingularMap (Functor.whiskerLeft (_root_.FundamentalGroupoid.map f.hom)
            (originalRegularDeckCoefficient Y y a)) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let α := CategoryTheory.regularPathInversePrecomposition
    (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)) a
  let β := originalRegularDeckCoefficient Y y a
  let η := singularFundamentalGroupoidNaturality f
  apply NatTrans.ext
  funext z
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  refine FreeAbelianGroup.lift_ext _ _ ?_
  intro γ
  let δ := singularRegularPathEquiv Y y (F.obj z) γ
  have h1 := CategoryTheory.regularPathInversePrecomposition_of _ a (F.obj z) γ
  have h2 := singularRegularPullbackCoefficientIso_hom_of f y z ((a⁻¹).asHom ≫ γ)
  have h3 := singularRegularPullbackCoefficientIso_hom_of f y z γ
  have h4 := originalRegularDeckCoefficient_of Y y a
    ((_root_.FundamentalGroupoid.map f.hom).obj ((singularFundamentalGroupoidFunctor X).obj z))
      (δ ≫ η.hom.app z)
  have hPath : singularRegularPathEquiv Y y (F.obj z) ((a⁻¹).asHom ≫ γ) ≫ η.hom.app z =
      ((singularRegularEndHom Y y a)⁻¹).asHom ≫ (δ ≫ η.hom.app z) :=
    (congrArg (fun h => h ≫ η.hom.app z)
      (singularRegularPathEquiv_inverse_precomposition Y y a (F.obj z) γ)).trans
        (Category.assoc _ _ _)
  change (singularRegularPullbackCoefficientIso f y).hom.app z
      (α.app (F.obj z) (FreeAbelianGroup.of γ)) =
    β.app _ ((singularRegularPullbackCoefficientIso f y).hom.app z (FreeAbelianGroup.of γ))
  exact (congrArg ((singularRegularPullbackCoefficientIso f y).hom.app z) h1).trans
    (h2.trans ((congrArg FreeAbelianGroup.of hPath).trans
      ((congrArg (β.app _) h3).trans h4).symm))

/-- The chain map on the original topological regular coefficients comes
from their actual coefficient natural transformation. -/
def originalRegularDeckChainMap (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk y)) ⟶
    localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk y)) :=
  SSet.localCoefficientChainMap (LocalSystem.toSingularMap (originalRegularDeckCoefficient Y y a))

/-- The original pulled-back chain action uses the same coefficient
transformation, whiskered along the original map of spaces. -/
def originalRegularPullbackDeckChainMap {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    localCoefficientChainComplex (LocalSystem.pullback f
      (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))) ⟶
    localCoefficientChainComplex (LocalSystem.pullback f
      (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))) :=
  SSet.localCoefficientChainMap (LocalSystem.toSingularMap
    (Functor.whiskerLeft (_root_.FundamentalGroupoid.map f.hom)
        (originalRegularDeckCoefficient Y y a)))

private theorem inverse_chain_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (a : A ⟶ A) (b : B ⟶ B) (h : a ≫ e.hom = e.hom ≫ b) :
    b ≫ e.inv = e.inv ≫ a := by
  apply (cancel_mono e.hom).mp
  have hL : (b ≫ e.inv) ≫ e.hom = b :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => b ≫ k) e.inv_hom_id).trans (Category.comp_id b))
  have hR : (e.inv ≫ a) ≫ e.hom = b :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => e.inv ≫ k) h).trans (e.inv_hom_id_assoc b))
  exact hL.trans hR.symm

/-- The actual original regular chain comparison is equivariant for
inverse precomposition and the original native deck map. -/
theorem originalTopRegularCoverChainIso_deck (Y : TopCat.{u}) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularDeckChainMap Y y a ≫ (originalTopRegularCoverChainIso Y y).hom =
      (originalTopRegularCoverChainIso Y y).hom ≫
        SSet.chainComplexMap (SSet.KanComplex.nativeCoverDeckMap a)
            (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let := TopCat.toSSet_obj_kanComplex Y
  let S := TopCat.toSSet.obj Y
  let ys : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let G := SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := S)
  let α := CategoryTheory.regularPathInversePrecomposition (SSet.FundamentalGroupoid.mk ys) a
  let β := LocalSystem.toSingularMap (originalRegularDeckCoefficient Y y a)
  let e := singularRegularCoefficientChainIso Y y
  let c := SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso S ys
  let A := SSet.localCoefficientChainMap α
  let B := originalRegularDeckChainMap Y y a
  let D := SSet.chainComplexMap (SSet.KanComplex.nativeCoverDeckMap a)
      (ModuleCat.of ℤ (ULift.{u} ℤ))
  have hCoeff : A ≫ e.hom = e.hom ≫ B :=
    (G.map_comp α (singularRegularCoefficientIso Y y).hom).symm.trans
      ((congrArg G.map (singularRegularCoefficientIso_inverse_precomposition Y y a)).trans
        (G.map_comp (singularRegularCoefficientIso Y y).hom β))
  have hInv : B ≫ e.inv = e.inv ≫ A := inverse_chain_square e A B hCoeff
  have hNative : A ≫ c.hom = c.hom ≫ D :=
    SSet.KanComplex.originalNativeRegularCoverChainIso_deck S ys a
  change B ≫ (e.inv ≫ c.hom) = (e.inv ≫ c.hom) ≫ D
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ c.hom) hInv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hNative).trans (Category.assoc _ _ _).symm)))

/-- The original pullback coefficient chain comparison has the same deck
square, including the existing nontrivial singular alignment. -/
theorem originalTopRegularPullbackCoverChainIso_deck {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularPullbackDeckChainMap f y a ≫ (originalTopRegularPullbackCoverChainIso f y).hom =
      (originalTopRegularPullbackCoverChainIso f y).hom ≫
        SSet.chainComplexMap (SSet.KanComplex.nativeRegularPullbackDeckMap
          (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) a)
              (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let := TopCat.toSSet_obj_kanComplex Y
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let sf := TopCat.toSSet.map f
  let ys : SY _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let G := SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := SX)
  let α := Functor.whiskerLeft (SSet.mapFundamentalGroupoid sf)
    (CategoryTheory.regularPathInversePrecomposition (SSet.FundamentalGroupoid.mk ys) a)
  let β := LocalSystem.toSingularMap (Functor.whiskerLeft (_root_.FundamentalGroupoid.map f.hom)
    (originalRegularDeckCoefficient Y y a))
  let e := singularRegularPullbackCoefficientChainIso f y
  let c := SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso sf ys
  let A := SSet.localCoefficientChainMap α
  let B := originalRegularPullbackDeckChainMap f y a
  let D := SSet.chainComplexMap (SSet.KanComplex.nativeRegularPullbackDeckMap sf ys a)
    (ModuleCat.of ℤ (ULift.{u} ℤ))
  have hCoeff : A ≫ e.hom = e.hom ≫ B :=
    (G.map_comp α (singularRegularPullbackCoefficientIso f y).hom).symm.trans
      ((congrArg G.map (singularRegularPullbackCoefficientIso_inverse_precomposition f y a)).trans
        (G.map_comp (singularRegularPullbackCoefficientIso f y).hom β))
  have hInv : B ≫ e.inv = e.inv ≫ A := inverse_chain_square e A B hCoeff
  have hNative : A ≫ c.hom = c.hom ≫ D :=
    SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso_deck sf ys a
  change B ≫ (e.inv ≫ c.hom) = (e.inv ≫ c.hom) ≫ D
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ c.hom) hInv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hNative).trans (Category.assoc _ _ _).symm)))

/-- The actual base-map chain morphism commutes with the same original
regular coefficient actions. -/
theorem originalRegularPullbackChainMap_deck_square {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularPullbackDeckChainMap f y a ≫ localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)) =
      localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)) ≫
          originalRegularDeckChainMap Y y a := by
  let L := CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)
  let m := localCoefficientPullbackChainMap f L
  let eS := originalTopRegularPullbackCoverChainIso f y
  let eT := originalTopRegularCoverChainIso Y y
  let A := originalRegularPullbackDeckChainMap f y a
  let B := originalRegularDeckChainMap Y y a
  let n := SSet.chainComplexMap
    (pullback.snd (TopCat.toSSet.map f) (SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y))) (ModuleCat.of ℤ (ULift.{u} ℤ))
  let Dp := SSet.chainComplexMap (SSet.KanComplex.nativeRegularPullbackDeckMap
    (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) a) (ModuleCat.of ℤ (ULift.{u} ℤ))
  let D := SSet.chainComplexMap (SSet.KanComplex.nativeCoverDeckMap a)
      (ModuleCat.of ℤ (ULift.{u} ℤ))
  let F := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj (ModuleCat.of ℤ (ULift.{u} ℤ))
  have hMap : m ≫ eT.hom = eS.hom ≫ n := originalTopRegularCoverChainMap_square f y
  have hS : A ≫ eS.hom = eS.hom ≫ Dp := originalTopRegularPullbackCoverChainIso_deck f y a
  have hT : B ≫ eT.hom = eT.hom ≫ D := originalTopRegularCoverChainIso_deck Y y a
  have hNative : Dp ≫ n = n ≫ D :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (SSet.KanComplex.nativeRegularPullbackDeckMap_snd
        (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) a)).trans (F.map_comp _ _))
  apply (cancel_mono eT.hom).mp
  have hL : (A ≫ m) ≫ eT.hom = eS.hom ≫ (Dp ≫ n) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => A ≫ k) hMap).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ n) hS).trans (Category.assoc _ _ _))))
  have hR : (m ≫ B) ≫ eT.hom = eS.hom ≫ (n ≫ D) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => m ≫ k) hT).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ D) hMap).trans (Category.assoc _ _ _))))
  exact hL.trans ((congrArg (fun k => eS.hom ≫ k) hNative).trans hR.symm)

/-- The actual original regular-relative chain endomorphism is induced on
its literal cokernel by inverse precomposition on both original complexes. -/
def originalRegularRelativeDeckChainMap {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularRelativeChainComplex f y ⟶ originalRegularRelativeChainComplex f y := by
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let e : originalRegularRelativeChainComplex f y ≅ cokernel m :=
    eqToIso (originalRegularRelativeChainComplex_eq_cokernel f y)
  let d : cokernel m ⟶ cokernel m :=
    cokernel.map m m (originalRegularPullbackDeckChainMap f y a)
      (originalRegularDeckChainMap Y y a) (originalRegularPullbackChainMap_deck_square f y a).symm
  exact e.hom ≫ d ≫ e.inv

/-- Its entire original quotient map is the same one used in the regular-relative construction. -/
theorem originalRegularRelativeDeckChainMap_projection {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularRelativeChainProjection f y ≫ originalRegularRelativeDeckChainMap f y a =
      originalRegularDeckChainMap Y y a ≫ originalRegularRelativeChainProjection f y := by
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let e : originalRegularRelativeChainComplex f y ≅ cokernel m :=
    eqToIso (originalRegularRelativeChainComplex_eq_cokernel f y)
  let B := originalRegularDeckChainMap Y y a
  let d : cokernel m ⟶ cokernel m :=
    cokernel.map m m (originalRegularPullbackDeckChainMap f y a) B
      (originalRegularPullbackChainMap_deck_square f y a).symm
  let q := originalRegularRelativeChainProjection f y
  have hQ : q ≫ e.hom = cokernel.π m :=
    originalRegularRelativeChainProjection_eq_cokernelπ f y
  have hMap : cokernel.π m ≫ d = B ≫ cokernel.π m := by
    dsimp only [d, cokernel.map]
    exact cokernel.π_desc _ _ _
  have hReturn : cokernel.π m ≫ e.inv = q :=
    (congrArg (fun t => t ≫ e.inv) hQ.symm).trans
      ((Category.assoc q e.hom e.inv).trans
        ((congrArg (fun t => q ≫ t) e.hom_inv_id).trans (Category.comp_id q)))
  change q ≫ (e.hom ≫ (d ≫ e.inv)) = B ≫ q
  have hL : q ≫ (e.hom ≫ (d ≫ e.inv)) = (cokernel.π m ≫ d) ≫ e.inv :=
    (Category.assoc q e.hom (d ≫ e.inv)).symm.trans
      ((congrArg (fun t => t ≫ (d ≫ e.inv)) hQ).trans
        (Category.assoc (cokernel.π m) d e.inv).symm)
  exact hL.trans ((congrArg (fun t => t ≫ e.inv) hMap).trans
    ((Category.assoc B (cokernel.π m) e.inv).trans
      (congrArg (fun t => B ≫ t) hReturn)))

/-- The actual paired deck map on the literal pulled covering arrow. -/
def originalRegularNativeDeckPair {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono f] (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularPulledCoverPair f y ⟶ originalRegularPulledCoverPair f y := by
  let p := originalRegularPulledCoverPair f y
  let l := SSet.KanComplex.nativeRegularPullbackDeckMap
    (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) a
  let r := SSet.KanComplex.nativeCoverDeckMap a
  have h : l ≫ p.hom = p.hom ≫ r :=
    (congrArg (fun t => l ≫ t) (originalRegularPulledCoverPair_hom f y)).trans
      ((SSet.KanComplex.nativeRegularPullbackDeckMap_snd
        (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y) a).trans
          (congrArg (fun t => t ≫ r) (originalRegularPulledCoverPair_hom f y).symm))
  exact SSetPair.homMk (X := p) (Y := p) l r h

/-- The original paired map retains its actual pulled-cover component. -/
theorem originalRegularNativeDeckPair_left {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono f] (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    (originalRegularNativeDeckPair f y a).hom.left =
      SSet.KanComplex.nativeRegularPullbackDeckMap (TopCat.toSSet.map f)
        (TopCat.toSSetObj₀Equiv.symm y) a := by
  dsimp only [originalRegularNativeDeckPair, SSetPair.homMk]
  rfl

/-- Its ambient component is the same actual native deck map. -/
theorem originalRegularNativeDeckPair_right {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono f] (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    (originalRegularNativeDeckPair f y a).hom.right = SSet.KanComplex.nativeCoverDeckMap a := by
  dsimp only [originalRegularNativeDeckPair, SSetPair.homMk]
  rfl

/-- The whole original relative-chain comparison intertwines the actual
regular coefficient action with the same paired deck map. -/
theorem originalRegularRelativeChainIso_deck {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono f] (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    originalRegularRelativeDeckChainMap f y a ≫ (originalRegularRelativeChainIso f y).hom =
      (originalRegularRelativeChainIso f y).hom ≫
        SSetPair.chainComplexMap (originalRegularNativeDeckPair f y a)
            (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let e := originalRegularRelativeChainIso f y
  let eT := originalTopRegularCoverChainIso Y y
  let q := originalRegularRelativeChainProjection f y
  let A := originalRegularRelativeDeckChainMap f y a
  let B := originalRegularDeckChainMap Y y a
  let p := originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let N := SSetPair.chainComplexMap (originalRegularNativeDeckPair f y a) R
  let D := SSet.chainComplexMap (SSet.KanComplex.nativeCoverDeckMap a) R
  let : Epi q := originalRegularRelativeChainProjection_epi f y
  have h1 : q ≫ A = B ≫ q := originalRegularRelativeDeckChainMap_projection f y a
  have h2 : q ≫ e.hom = eT.hom ≫ p.chainComplexπ R := originalRegularRelativeChainIso_projection f y
  have h3 : B ≫ eT.hom = eT.hom ≫ D := originalTopRegularCoverChainIso_deck Y y a
  let t := originalRegularNativeDeckPair f y a
  let F := (SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R
  let G := (SSetPair.chainComplexFunctorRight (ModuleCat.{u} ℤ)).obj R
  let η := (SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R
  have hπ : η.app p = p.chainComplexπ R := rfl
  have hF : F.map t = N := rfl
  have hG : G.map t = SSet.chainComplexMap t.hom.right R := rfl
  have hRight : G.map t = D := hG.trans
    (congrArg (fun k => SSet.chainComplexMap k R) (originalRegularNativeDeckPair_right f y a))
  have hNat : G.map t ≫ η.app p = η.app p ≫ F.map t := η.naturality t
  have h4 : p.chainComplexπ R ≫ N = D ≫ p.chainComplexπ R :=
    (congrArg₂ (fun a b => a ≫ b) hπ.symm hF.symm).trans
      (hNat.symm.trans (congrArg₂ (fun a b => a ≫ b) hRight hπ))
  apply (cancel_epi q).mp
  have hL : q ≫ (A ≫ e.hom) = eT.hom ≫ (D ≫ p.chainComplexπ R) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ e.hom) h1).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => B ≫ k) h2).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun k => k ≫ p.chainComplexπ R) h3).trans (Category.assoc _ _ _))))))
  have hR : q ≫ (e.hom ≫ N) = eT.hom ≫ (p.chainComplexπ R ≫ N) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ N) h2).trans (Category.assoc _ _ _))
  exact hL.trans ((congrArg (fun k => eT.hom ≫ k) h4.symm).trans hR.symm)

/-- Equivariance retains the actual original homology action in every degree. -/
theorem originalRegularRelativeHomologyIso_deck {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono f] (y : Y)
    (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) (n : ℕ) :
    HomologicalComplex.homologyMap (originalRegularRelativeDeckChainMap f y a) n ≫
        (originalRegularRelativeHomologyIso f y n).hom =
      (originalRegularRelativeHomologyIso f y n).hom ≫
        SSetPair.homologyMap (originalRegularNativeDeckPair f y a)
            (ModuleCat.of ℤ (ULift.{u} ℤ)) n := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n
  rw [originalRegularRelativeHomologyIso_hom]
  change H.map (originalRegularRelativeDeckChainMap f y a) ≫
      H.map (originalRegularRelativeChainIso f y).hom =
    H.map (originalRegularRelativeChainIso f y).hom ≫
      H.map (SSetPair.chainComplexMap (originalRegularNativeDeckPair f y a)
        (ModuleCat.of ℤ (ULift.{u} ℤ)))
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (originalRegularRelativeChainIso_deck f y a)).trans (H.map_comp _ _))

end TopCat

end
