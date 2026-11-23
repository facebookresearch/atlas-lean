/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularPathDeckNaturality
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Pullback comparisons for native simplicial covers

A simplicial map induces a comparison from its native cover to the pullback of
the target cover, with explicit projection equations. This comparison is an
isomorphism when the induced fundamental-groupoid functor is full and faithful.
For Kan complexes, the cover maps also commute with the deck actions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

public section

namespace SSet.KanComplex

/-- The actual native map, paired with its unchanged original projection,
defines the canonical comparison to the pulled-back target cover. -/
def nativeCoverCartesianComparison {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCover X x ⟶ pullback f (nativeCoverProjection Y (f.app (op ⦋0⦌) x)) :=
  pullback.lift (nativeCoverProjection X x) (nativeCoverMap f x)
    (nativeCoverMap_projection f x).symm

/-- The comparison retains the original source projection. -/
theorem nativeCoverCartesianComparison_fst {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCoverCartesianComparison f x ≫ pullback.fst f
      (nativeCoverProjection Y (f.app (op ⦋0⦌) x)) = nativeCoverProjection X x :=
  pullback.lift_fst _ _ _

/-- Its second component is the SAME original induced native map. -/
theorem nativeCoverCartesianComparison_snd {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCoverCartesianComparison f x ≫ pullback.snd f
      (nativeCoverProjection Y (f.app (op ⦋0⦌) x)) = nativeCoverMap f x :=
  pullback.lift_snd _ _ _

private theorem vertexPath_transport {Y : SSet.{u}} {y z w : Y _⦋0⦌}
    (h : z = w)
    (v : {v : (nativeCover Y y) _⦋0⦌ // (nativeCoverProjection Y y).app (op ⦋0⦌) v = z}) :
    nativeCoverVertexPathEquiv w (⟨v.val, v.property.trans h⟩ :
      {v : (nativeCover Y y) _⦋0⦌ // (nativeCoverProjection Y y).app (op ⦋0⦌) v = w}) =
      nativeCoverVertexPathEquiv z v ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk h) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

private def mappedNativeSimplexLift {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) {n : ℕ}
    (sigma : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x // L ≫ nativeCoverProjection X x = sigma}) :
    {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y (f.app (op ⦋0⦌) x) //
      L ≫ nativeCoverProjection Y (f.app (op ⦋0⦌) x) = sigma ≫ f} :=
  ⟨L.val ≫ nativeCoverMap f x,
    (Category.assoc L.val (nativeCoverMap f x) _).trans
      ((congrArg (fun k => L.val ≫ k) (nativeCoverMap_projection f x)).trans
        ((Category.assoc L.val (nativeCoverProjection X x) f).symm.trans
          (congrArg (fun k => k ≫ f) L.property)))⟩

/-- Native base change applies the original fundamental-groupoid map to
EVERY lifted simplex path, with its actual endpoint cast. -/
private theorem nativeCoverSimplexFiberPathEquiv_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) {n : ℕ}
    (sigma : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x // L ≫ nativeCoverProjection X x = sigma}) :
    nativeCoverSimplexFiberPathEquiv (sigma ≫ f) (mappedNativeSimplexLift f x sigma L) =
      (SSet.mapFundamentalGroupoid f).map (nativeCoverSimplexFiberPathEquiv sigma L) ≫
        eqToHom (regularLocalCoefficientPullbackEndpoint_eq f sigma) := by
  let alpha : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))
  let z := SSet.yonedaEquiv (alpha ≫ sigma)
  let w := SSet.yonedaEquiv (alpha ≫ (sigma ≫ f))
  let v := nativeCoverSimplexFiberVertexEquiv sigma L
  let M := mappedNativeSimplexLift f x sigma L
  let vY := nativeCoverSimplexFiberVertexEquiv (sigma ≫ f) M
  have hw : f.app (op ⦋0⦌) z = w :=
    (SSet.yonedaEquiv_comp (alpha ≫ sigma) f).symm.trans
      (congrArg SSet.yonedaEquiv (Category.assoc alpha sigma f))
  let vMap : {v : (nativeCover Y (f.app (op ⦋0⦌) x)) _⦋0⦌ //
      (nativeCoverProjection Y (f.app (op ⦋0⦌) x)).app (op ⦋0⦌) v = f.app (op ⦋0⦌) z} :=
    ⟨(nativeCoverMap f x).app (op ⦋0⦌) v.val,
      (congrArg (fun k : nativeCover X x ⟶ Y => k.app (op ⦋0⦌) v.val)
        (nativeCoverMap_projection f x)).trans
        (congrArg (f.app (op ⦋0⦌)) v.property)⟩
  have hval : vY.val = vMap.val :=
    (nativeCoverSimplexFiberVertexEquiv_apply (sigma ≫ f) M).trans
      ((congrArg SSet.yonedaEquiv (Category.assoc alpha L.val (nativeCoverMap f x)).symm).trans
        ((SSet.yonedaEquiv_comp (alpha ≫ L.val) (nativeCoverMap f x)).symm.trans
          (congrArg ((nativeCoverMap f x).app (op ⦋0⦌))
            (nativeCoverSimplexFiberVertexEquiv_apply sigma L).symm)))
  have hVertex : vY =
      (⟨vMap.val, vMap.property.trans hw⟩ :
        {v : (nativeCover Y (f.app (op ⦋0⦌) x)) _⦋0⦌ //
          (nativeCoverProjection Y (f.app (op ⦋0⦌) x)).app (op ⦋0⦌) v = w}) := Subtype.ext hval
  have hTransport : nativeCoverVertexPathEquiv w vY =
      nativeCoverVertexPathEquiv (f.app (op ⦋0⦌) z) vMap ≫
        eqToHom (congrArg SSet.FundamentalGroupoid.mk hw) :=
    (congrArg (nativeCoverVertexPathEquiv w) hVertex).trans (vertexPath_transport hw vMap)
  have hPath : nativeCoverVertexPathEquiv (f.app (op ⦋0⦌) z) vMap =
      (SSet.mapFundamentalGroupoid f).map (nativeCoverVertexPathEquiv z v) :=
    nativeCoverVertexPathEquiv_map f x z v
  exact hTransport.trans
    (congrArg (fun k => k ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk hw)) hPath)

private def nativeCoverPathMapEquiv {X Y : SSet.{u}} (f : X ⟶ Y)
    [(SSet.mapFundamentalGroupoid f).Full] [(SSet.mapFundamentalGroupoid f).Faithful]
    (x : X _⦋0⦌) {n : ℕ} (sigma : (Δ[n] : SSet.{u}) ⟶ X) :
    (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk
      (SSet.yonedaEquiv ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
        (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ sigma))) ≃
    (SSet.FundamentalGroupoid.mk (f.app (op ⦋0⦌) x) ⟶ SSet.FundamentalGroupoid.mk
      (SSet.yonedaEquiv ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
        (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ (sigma ≫ f)))) where
  toFun gamma := (SSet.mapFundamentalGroupoid f).map gamma ≫
    eqToHom (regularLocalCoefficientPullbackEndpoint_eq f sigma)
  invFun gamma := (SSet.mapFundamentalGroupoid f).preimage
    (gamma ≫ eqToHom (regularLocalCoefficientPullbackEndpoint_eq f sigma).symm)
  left_inv gamma := by
    let F := SSet.mapFundamentalGroupoid f
    let h := regularLocalCoefficientPullbackEndpoint_eq f sigma
    apply (SSet.mapFundamentalGroupoid f).map_injective
    change F.map (F.preimage ((F.map gamma ≫ eqToHom h) ≫ eqToHom h.symm)) = F.map gamma
    rw [F.map_preimage]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  right_inv gamma := by
    let F := SSet.mapFundamentalGroupoid f
    let h := regularLocalCoefficientPullbackEndpoint_eq f sigma
    change F.map (F.preimage (gamma ≫ eqToHom h.symm)) ≫ eqToHom h = gamma
    have hMap : F.map (F.preimage (gamma ≫ eqToHom h.symm)) =
        gamma ≫ eqToHom h.symm := F.map_preimage (gamma ≫ eqToHom h.symm)
    rw [hMap]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private def mappedCartesianSimplexLift {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) {n : ℕ}
    (sigma : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x // L ≫ nativeCoverProjection X x = sigma}) :
    {M : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y (f.app (op ⦋0⦌) x)) //
      M ≫ pullback.fst f (nativeCoverProjection Y (f.app (op ⦋0⦌) x)) = sigma} :=
  ⟨L.val ≫ nativeCoverCartesianComparison f x,
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => L.val ≫ k) (nativeCoverCartesianComparison_fst f x)).trans L.property)⟩

private theorem mappedCartesianSimplexLift_path {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) {n : ℕ}
    (sigma : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x // L ≫ nativeCoverProjection X x = sigma}) :
    nativeCoverPullbackSimplexPathEquiv f (f.app (op ⦋0⦌) x) sigma
        (mappedCartesianSimplexLift f x sigma L) =
      (SSet.mapFundamentalGroupoid f).map (nativeCoverSimplexFiberPathEquiv sigma L) ≫
        eqToHom (regularLocalCoefficientPullbackEndpoint_eq f sigma) := by
  let M := mappedCartesianSimplexLift f x sigma L
  let N := mappedNativeSimplexLift f x sigma L
  have h : nativeCoverPullbackSimplexFiberEquiv f (f.app (op ⦋0⦌) x) sigma M = N := by
    apply Subtype.ext
    exact (Category.assoc L.val (nativeCoverCartesianComparison f x) _).trans
      (congrArg (fun k => L.val ≫ k) (nativeCoverCartesianComparison_snd f x))
  change nativeCoverSimplexFiberPathEquiv (sigma ≫ f)
    (nativeCoverPullbackSimplexFiberEquiv f (f.app (op ⦋0⦌) x) sigma M) = _
  exact (congrArg (nativeCoverSimplexFiberPathEquiv (sigma ≫ f)) h).trans
    (nativeCoverSimplexFiberPathEquiv_map f x sigma L)

private theorem nativeCoverCartesianComparison_on_generator {X Y : SSet.{u}} (f : X ⟶ Y)
    [(SSet.mapFundamentalGroupoid f).Full] [(SSet.mapFundamentalGroupoid f).Faithful]
    (x : X _⦋0⦌) (n : ℕ) (g : nativeCoverSimplexPathGenerators X x n) :
    (nativeCoverCartesianComparison f x).app (op ⦋n⦌)
        (nativeCoverSimplexPathGeneratorsEquiv X x n g) =
      nativeCoverPullbackSimplexPathGeneratorsEquiv f (f.app (op ⦋0⦌) x) n
        ⟨g.1, nativeCoverPathMapEquiv f x g.1 g.2⟩ := by
  rcases g with ⟨sigma, gamma⟩
  let E := nativeCoverPullbackSimplexPathEquiv f (f.app (op ⦋0⦌) x) sigma
  let L := (nativeCoverSimplexFiberPathEquiv (X := X) (x := x) sigma).symm gamma
  let M := mappedCartesianSimplexLift f x sigma L
  let hgamma := nativeCoverPathMapEquiv f x sigma gamma
  have hPath : E M = hgamma :=
    (mappedCartesianSimplexLift_path f x sigma L).trans
      (congrArg (fun k => (SSet.mapFundamentalGroupoid f).map k ≫
        eqToHom (regularLocalCoefficientPullbackEndpoint_eq f sigma))
          ((nativeCoverSimplexFiberPathEquiv sigma).apply_symm_apply gamma))
  have hM : M = E.symm hgamma :=
    E.injective (hPath.trans (E.apply_symm_apply hgamma).symm)
  have hL := nativeCoverSimplexPathGeneratorsEquiv_apply X x n sigma gamma
  have hR := nativeCoverPullbackSimplexPathGeneratorsEquiv_apply f (f.app (op ⦋0⦌) x) n
    (⟨sigma, hgamma⟩ : nativeCoverPullbackSimplexPathGenerators f (f.app (op ⦋0⦌) x) n)
  exact (congrArg ((nativeCoverCartesianComparison f x).app (op ⦋n⦌)) hL).trans
    ((SSet.yonedaEquiv_comp L.val (nativeCoverCartesianComparison f x)).symm.trans
      ((congrArg SSet.yonedaEquiv (congrArg Subtype.val hM)).trans hR.symm))

/-- Full faithfulness of the actual fundamental-groupoid map makes the SAME
native-cover comparison an isomorphism, via every actual simplex/path
coordinate. No expected cover or coherent lift family is supplied. -/
theorem nativeCoverCartesianComparison_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [(SSet.mapFundamentalGroupoid f).Full] [(SSet.mapFundamentalGroupoid f).Faithful]
    (x : X _⦋0⦌) : IsIso (nativeCoverCartesianComparison f x) := by
  let c := nativeCoverCartesianComparison f x
  let : ∀ d, IsIso (c.app d) := fun d => by
    rcases d with ⟨⟨n⟩⟩
    let E := nativeCoverSimplexPathGeneratorsEquiv X x n
    let H := nativeCoverPullbackSimplexPathGeneratorsEquiv f (f.app (op ⦋0⦌) x) n
    let M : nativeCoverSimplexPathGenerators X x n ≃
        nativeCoverPullbackSimplexPathGenerators f (f.app (op ⦋0⦌) x) n :=
      Equiv.sigmaCongrRight (fun sigma => nativeCoverPathMapEquiv f x sigma)
    let e := E.symm.trans (M.trans H)
    have hc : (fun s => c.app (op ⦋n⦌) s) = fun s => e s := by
      funext s
      obtain ⟨g, rfl⟩ := E.surjective s
      have h := nativeCoverCartesianComparison_on_generator f x n g
      have he : e (E g) = H (M g) :=
        congrArg (fun k => H (M k)) (E.symm_apply_apply g)
      exact h.trans he.symm
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun s => c.app (op ⦋n⦌) s)
    exact hc.symm ▸ e.bijective
  exact NatIso.isIso_of_isIso_app c

/-- The computed isomorphism has precisely the original native map as its
second component, and the unchanged base projection as its first. -/
def nativeCoverCartesianComparisonIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [(SSet.mapFundamentalGroupoid f).Full] [(SSet.mapFundamentalGroupoid f).Faithful]
    (x : X _⦋0⦌) :
    nativeCover X x ≅ pullback f (nativeCoverProjection Y (f.app (op ⦋0⦌) x)) := by
  letI := nativeCoverCartesianComparison_isIso f x
  exact asIso (nativeCoverCartesianComparison f x)

/-- The same original induced native map intertwines the genuine LEFT
deck actions through its original fundamental-groupoid endomorphism map. -/
theorem nativeCoverMap_deck {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverDeckMap a ≫ nativeCoverMap f x =
      nativeCoverMap f x ≫ nativeCoverDeckMap
        ((SSet.mapFundamentalGroupoid f).mapEnd (SSet.FundamentalGroupoid.mk x) a) := by
  let F := SSet.mapFundamentalGroupoid f
  let y := f.app (op ⦋0⦌) x
  let dx := nativeCoverDeckMap a
  let ay := F.mapEnd (SSet.FundamentalGroupoid.mk x) a
  let dy := nativeCoverDeckMap ay
  let c := nativeCoverMap f x
  have hInv : F.map (a⁻¹).asHom = (ay⁻¹).asHom := by
    change (F.mapEnd (SSet.FundamentalGroupoid.mk x) (a⁻¹)).asHom = (ay⁻¹).asHom
    exact congrArg (fun b : End (F.obj (SSet.FundamentalGroupoid.mk x)) => b.asHom)
      ((F.mapEnd (SSet.FundamentalGroupoid.mk x)).map_inv a)
  have hom_eq : ∀ (n : ℕ) (L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x),
      (L ≫ dx) ≫ c = (L ≫ c) ≫ dy := by
    intro n L
    let sigma := L ≫ nativeCoverProjection X x
    let A : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x // L ≫ nativeCoverProjection X x =
        sigma} := ⟨L, rfl⟩
    let Ad := nativeCoverDeckedSimplexLift x a sigma A
    let B := mappedNativeSimplexLift f x sigma A
    let AB := mappedNativeSimplexLift f x sigma Ad
    let BA := nativeCoverDeckedSimplexLift y ay (sigma ≫ f) B
    let gamma := nativeCoverSimplexFiberPathEquiv (X := X) (x := x) sigma A
    let e := nativeCoverSimplexFiberPathEquiv (X := Y) (x := y) (sigma ≫ f)
    let chi := eqToHom (regularLocalCoefficientPullbackEndpoint_eq f sigma)
    have hAB : e AB = (ay⁻¹).asHom ≫ (F.map gamma ≫ chi) :=
      (nativeCoverSimplexFiberPathEquiv_map f x sigma Ad).trans
        ((congrArg (fun k => F.map k ≫ chi)
          (nativeCoverSimplexFiberPathEquiv_deck x a sigma A)).trans
            ((congrArg (fun k => k ≫ chi) (F.map_comp (a⁻¹).asHom gamma)).trans
              ((congrArg (fun k => (k ≫ F.map gamma) ≫ chi) hInv).trans
                (Category.assoc _ _ _))))
    have hBA : e BA = (ay⁻¹).asHom ≫ (F.map gamma ≫ chi) :=
      (nativeCoverSimplexFiberPathEquiv_deck y ay (sigma ≫ f) B).trans
        (congrArg (fun k => (ay⁻¹).asHom ≫ k)
          (nativeCoverSimplexFiberPathEquiv_map f x sigma A))
    have hAd : Ad.val = L ≫ dx := nativeCoverDeckedSimplexLift_val x a sigma A
    have hABval : AB.val = (L ≫ dx) ≫ c :=
      (show AB.val = Ad.val ≫ c from rfl).trans (congrArg (fun t => t ≫ c) hAd)
    have hBval : B.val = L ≫ c := rfl
    have hBAval : BA.val = (L ≫ c) ≫ dy :=
      (nativeCoverDeckedSimplexLift_val y ay (sigma ≫ f) B).trans
        (congrArg (fun t => t ≫ dy) hBval)
    exact hABval.symm.trans
      ((congrArg Subtype.val (e.injective (hAB.trans hBA.symm))).trans hBAval)
  apply NatTrans.ext
  funext d
  rcases d with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  let L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x := SSet.yonedaEquiv.symm s
  have h : L ≫ (dx ≫ c) = L ≫ (c ≫ dy) :=
    (Category.assoc _ _ _).symm.trans ((hom_eq n L).trans (Category.assoc _ _ _))
  have hv := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, L, Equiv.apply_symm_apply] using hv

end SSet.KanComplex

end
