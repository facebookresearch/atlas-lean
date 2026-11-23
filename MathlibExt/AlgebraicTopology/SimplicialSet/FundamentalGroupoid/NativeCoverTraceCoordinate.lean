/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverHomotopyLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy

/-!
# The original root coordinate of a lifted homotopy

An edge from the actual identity point of the native cover records its
endpoint's original path coordinate. This follows from the defining Under
triangle and the original pullback square. It identifies the endpoint of an
actual lifted self-homotopy with the saved inverse-precomposition deck map.
No cover coordinate or endpoint equality is supplied as a hypothesis to the
H-space application.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

public section

namespace SSet.KanComplex

private theorem underIdentityArrow_chain {C : Type u} [Category.{v} C]
    (x : C) (A U : Under x) (hA : A = Under.mk (𝟙 x)) (f : A ⟶ U) :
    (ComposableArrows.mk₁ ((Under.forget x).map f) : ComposableArrows C 1) =
      ComposableArrows.mk₁ U.hom := by
  subst A
  have hw : (𝟙 x) ≫ f.right = U.hom := Under.w f
  have hf : (Under.forget x).map f = U.hom :=
    (Category.id_comp f.right).symm.trans hw
  exact congrArg (fun k : x ⟶ U.right => ComposableArrows.mk₁ k) hf

/-- Every actual edge from the identity point has the original endpoint path
coordinate, expressed as a whole degree-one nerve simplex. -/
theorem nativeCoverVertexPathEquiv_edge_chain {X : SSet.{u}}
    (x z : X _⦋0⦌)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (op ⦋0⦌) v = z})
    (e : (nativeCover X x).Edge (nativeCoverIdentityPoint X x) v.val) :
    (ComposableArrows.mk₁ (nativeCoverVertexPathEquiv z v) :
        (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) _⦋1⦌) =
      (nativeCoverUnit X).app (op ⦋1⦌)
        ((nativeCoverProjection X x).app (op ⦋1⦌) e.edge) := by
  let G := SSet.FundamentalGroupoid X
  let a : G := SSet.FundamentalGroupoid.mk x
  let P := nativeCover X x
  let A := CategoryTheory.nerve (Under a)
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let q : A ⟶ CategoryTheory.nerve G := nativeCoverNerveProjection X x
  let b := nativeCoverIdentityPoint X x
  let er : A.Edge (r.app (op ⦋0⦌) b) (r.app (op ⦋0⦌) v.val) := e.map r
  let A₀ : Under a := CategoryTheory.nerveEquiv (r.app (op ⦋0⦌) b)
  let U : Under a := CategoryTheory.nerveEquiv (r.app (op ⦋0⦌) v.val)
  let f : A₀ ⟶ U := CategoryTheory.nerve.homEquiv er
  have hA : A₀ = Under.mk (𝟙 a) :=
    (congrArg (CategoryTheory.nerveEquiv (C := Under a))
      (nativeCoverUnderProjection_identityPoint X x)).trans (by rfl)
  have hEdge : er.edge = (ComposableArrows.mk₁ f : A _⦋1⦌) := by
    have h := congrArg (fun t : A.Edge (r.app (op ⦋0⦌) b)
        (r.app (op ⦋0⦌) v.val) => t.edge)
      ((CategoryTheory.nerve.homEquiv (C := Under a)).symm_apply_apply er)
    exact h.symm
  have hForgot : q.app (op ⦋1⦌) er.edge =
      (ComposableArrows.mk₁ U.hom : (CategoryTheory.nerve G) _⦋1⦌) := by
    let R1 := (CategoryTheory.nerve G) _⦋1⦌
    have h1 : (q.app (op ⦋1⦌) er.edge : R1) =
        q.app (op ⦋1⦌) (ComposableArrows.mk₁ f) :=
      congrArg (q.app (op ⦋1⦌)) hEdge
    have h2 : (q.app (op ⦋1⦌) (ComposableArrows.mk₁ f) : R1) =
        (ComposableArrows.mk₁ ((Under.forget a).map f) : R1) :=
      CategoryTheory.nerveMap_app_mk₁ (Under.forget a) f
    have h3 : (ComposableArrows.mk₁ ((Under.forget a).map f) : R1) =
        (ComposableArrows.mk₁ U.hom : R1) := underIdentityArrow_chain a A₀ U hA f
    exact h1.trans (h2.trans h3)
  let V := nativeCoverVertexUnderEquiv (X := X) (x := x) z v
  have hV : V.val = U := nativeCoverVertexUnderEquiv_val z v
  have hCoordinate : (ComposableArrows.mk₁ (nativeCoverVertexPathEquiv z v) :
      (CategoryTheory.nerve G) _⦋1⦌) = ComposableArrows.mk₁ U.hom := by
    calc
      ComposableArrows.mk₁ (nativeCoverVertexPathEquiv z v) =
          ComposableArrows.mk₁ (V.val.hom ≫ eqToHom V.property) :=
        congrArg (fun k : a ⟶ SSet.FundamentalGroupoid.mk z => ComposableArrows.mk₁ k)
          (nativeCoverVertexPathEquiv_apply z v)
      _ = ComposableArrows.mk₁ V.val.hom :=
        ComposableArrows.mk₁_comp_eqToHom V.val.hom V.property
      _ = ComposableArrows.mk₁ U.hom :=
        congrArg (fun T : Under a => (ComposableArrows.mk₁ T.hom :
          (CategoryTheory.nerve G) _⦋1⦌)) hV
  have hSquare : p ≫ nativeCoverUnit X = r ≫ q := by
    dsimp only [p, r, q, nativeCover, nativeCoverProjection, nativeCoverUnderProjection]
    exact pullback.condition
  have hAt : (nativeCoverUnit X).app (op ⦋1⦌) (p.app (op ⦋1⦌) e.edge) =
      q.app (op ⦋1⦌) er.edge :=
    congrArg (fun k : P ⟶ CategoryTheory.nerve G => k.app (op ⦋1⦌) e.edge) hSquare
  exact hCoordinate.trans (hForgot.symm.trans hAt.symm)

private theorem homotopyTrace_edge_computation {A B : SSet.{u}}
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (x : A _⦋0⦌) :
    (SSet.Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x).edge =
      (((SSet.yonedaEquiv (X := A) (n := ⦋0⦌)).symm x ▷ (Δ[1] : SSet.{u})) ≫ H.h).app
        (op ⦋1⦌) (SSet.prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1 := by
  rfl

private theorem liftedHomotopyTrace_edge {X : SSet.{u}} (x : X _⦋0⦌)
    (H : SSet.Homotopy (𝟙 X) (𝟙 X))
    (f : nativeCover X x ⟶ nativeCover X x)
    (K : SSet.Homotopy (𝟙 (nativeCover X x)) f)
    (hProjection : K.h ≫ nativeCoverProjection X x =
      (nativeCoverProjection X x ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    (nativeCoverProjection X x).app (op ⦋1⦌)
      (SSet.Edge.ofSimplicialObjectHomotopy K.toSimplicialObjectHomotopy
        (nativeCoverIdentityPoint X x)).edge =
      (SSet.Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x).edge := by
  let P := nativeCover X x
  let p := nativeCoverProjection X x
  let b := nativeCoverIdentityPoint X x
  let j : (Δ[0] : SSet.{u}) ⟶ P := SSet.yonedaEquiv.symm b
  let jX : (Δ[0] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm x
  have hPoint : j ≫ p = jX :=
    (SSet.yonedaEquiv_symm_comp b p).trans
      (congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm
        (nativeCoverProjection_identityPoint X x))
  have hCylinder : ((j ▷ (Δ[1] : SSet.{u})) ≫ K.h) ≫ p =
      (jX ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
    calc
      ((j ▷ (Δ[1] : SSet.{u})) ≫ K.h) ≫ p =
          (j ▷ (Δ[1] : SSet.{u})) ≫ (K.h ≫ p) := Category.assoc _ _ _
      _ = (j ▷ (Δ[1] : SSet.{u})) ≫
          ((p ▷ (Δ[1] : SSet.{u})) ≫ H.h) :=
        congrArg (fun k => (j ▷ (Δ[1] : SSet.{u})) ≫ k) hProjection
      _ = ((j ≫ p) ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ H.h) (comp_whiskerRight j p (Δ[1] : SSet.{u})).symm)
      _ = (jX ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
        congrArg (fun k => (k ▷ (Δ[1] : SSet.{u})) ≫ H.h) hPoint
  rw [homotopyTrace_edge_computation, homotopyTrace_edge_computation]
  exact congrArg (fun k : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ X =>
    k.app (op ⦋1⦌) (SSet.prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1) hCylinder

/-- The endpoint's actual path coordinate is the original projected homotopy
trace. The equality of whole cylinder maps is retained. -/
theorem nativeCover_liftedSelfHomotopy_rootCoordinate {X : SSet.{u}}
    (x : X _⦋0⦌) (H : SSet.Homotopy (𝟙 X) (𝟙 X))
    (f : nativeCover X x ⟶ nativeCover X x)
    (K : SSet.Homotopy (𝟙 (nativeCover X x)) f)
    (hProjection : K.h ≫ nativeCoverProjection X x =
      (nativeCoverProjection X x ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    (hEnd : f ≫ nativeCoverProjection X x = nativeCoverProjection X x) :
    nativeCoverVertexPathEquiv x
      (⟨f.app (op ⦋0⦌) (nativeCoverIdentityPoint X x),
        (congrArg (fun k => k.app (op ⦋0⦌) (nativeCoverIdentityPoint X x)) hEnd).trans
          (nativeCoverProjection_identityPoint X x)⟩ :
        {v : (nativeCover X x) _⦋0⦌ //
          (nativeCoverProjection X x).app (op ⦋0⦌) v = x}) =
      SSet.FundamentalGroupoid.homMk
        (SSet.Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x) := by
  let b := nativeCoverIdentityPoint X x
  let V : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (op ⦋0⦌) v = x} :=
    ⟨f.app (op ⦋0⦌) b,
      (congrArg (fun k => k.app (op ⦋0⦌) b) hEnd).trans
        (nativeCoverProjection_identityPoint X x)⟩
  let E : (nativeCover X x).Edge b V.val :=
    SSet.Edge.ofSimplicialObjectHomotopy K.toSimplicialObjectHomotopy b
  let e : X.Edge x x :=
    SSet.Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x
  have hChain : (ComposableArrows.mk₁ (nativeCoverVertexPathEquiv x V) :
      (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) _⦋1⦌) =
      ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) :=
    (nativeCoverVertexPathEquiv_edge_chain x x V E).trans
      ((congrArg ((nativeCoverUnit X).app (op ⦋1⦌))
          (liftedHomotopyTrace_edge x H f K hProjection)).trans
        (SSet.fundamentalGroupoidNerveEquiv_app_edge X (SSet.FundamentalGroupoid X)
          (𝟭 (SSet.FundamentalGroupoid X)) e))
  exact CategoryTheory.Arrow.mk_injective _ _
    (congrArg CategoryTheory.ComposableArrows.arrowEquiv hChain)

/-- The actual deck image of the original root has exactly the saved inverse
path coordinate, with no normalization of another first path. -/
theorem nativeCoverDeckMap_rootCoordinate {X : SSet.{u}} (x : X _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverVertexPathEquiv x
      (⟨(nativeCoverDeckMap g).app (op ⦋0⦌) (nativeCoverIdentityPoint X x),
        (congrArg (fun k => k.app (op ⦋0⦌) (nativeCoverIdentityPoint X x))
          (nativeCoverDeckMap_projection g)).trans
          (nativeCoverProjection_identityPoint X x)⟩ :
        {v : (nativeCover X x) _⦋0⦌ //
          (nativeCoverProjection X x).app (op ⦋0⦌) v = x}) = (g⁻¹).asHom := by
  let a := SSet.FundamentalGroupoid.mk x
  let A := Under a
  let P := nativeCover X x
  let r : P ⟶ CategoryTheory.nerve A := nativeCoverUnderProjection X x
  let b := nativeCoverIdentityPoint X x
  let V : {v : P _⦋0⦌ // (nativeCoverProjection X x).app (op ⦋0⦌) v = x} :=
    ⟨(nativeCoverDeckMap g).app (op ⦋0⦌) b,
      (congrArg (fun k => k.app (op ⦋0⦌) b) (nativeCoverDeckMap_projection g)).trans
        (nativeCoverProjection_identityPoint X x)⟩
  have hUnder : r.app (op ⦋0⦌) V.val =
      ComposableArrows.mk₀ (Under.mk (g⁻¹).asHom) := by
    let R0 := (CategoryTheory.nerve A) _⦋0⦌
    let d := (CategoryTheory.nerveMap (Under.map (g⁻¹).asHom)).app (op ⦋0⦌)
    have h1 : (r.app (op ⦋0⦌) V.val : R0) = d (r.app (op ⦋0⦌) b) :=
      congrArg (fun k => k.app (op ⦋0⦌) b) (nativeCoverDeckMap_underProjection g)
    have h2 : d (r.app (op ⦋0⦌) b) =
        d (ComposableArrows.mk₀ (Under.mk (𝟙 a)) : R0) :=
      congrArg d (nativeCoverUnderProjection_identityPoint X x)
    have h3 : d (ComposableArrows.mk₀ (Under.mk (𝟙 a)) : R0) =
        (ComposableArrows.mk₀ (Under.mk (g⁻¹).asHom) : R0) := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      congr 1
      change Under.mk ((g⁻¹).asHom ≫ 𝟙 a) = Under.mk (g⁻¹).asHom
      rw [Category.comp_id]
    exact h1.trans (h2.trans h3)
  have hV : nativeCoverVertexUnderEquiv x V =
      (⟨Under.mk (g⁻¹).asHom, rfl⟩ : {U : A // U.right = a}) := by
    apply Subtype.ext
    exact (nativeCoverVertexUnderEquiv_val x V).trans
      ((congrArg (CategoryTheory.nerveEquiv (C := A)) hUnder).trans (by rfl))
  have hCoordinate := nativeCoverVertexPathEquiv_apply x V
  rw [hV] at hCoordinate
  exact hCoordinate.trans (Category.comp_id (g⁻¹).asHom)

/-- A lifted identity self-homotopy with the original inverse-End trace ends
at the actual saved deck map, as an equality of entire maps. -/
theorem nativeCover_liftedSelfHomotopy_endpoint_eq_deck {X : SSet.{u}}
    [SSet.KanComplex X] (x : X _⦋0⦌) (H : SSet.Homotopy (𝟙 X) (𝟙 X))
    (g : End (SSet.FundamentalGroupoid.mk x))
    (hTrace : SSet.FundamentalGroupoid.homMk
      (SSet.Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x) = (g⁻¹).asHom)
    (f : nativeCover X x ⟶ nativeCover X x)
    (K : SSet.Homotopy (𝟙 (nativeCover X x)) f)
    (hProjection : K.h ≫ nativeCoverProjection X x =
      (nativeCoverProjection X x ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    (hEnd : f ≫ nativeCoverProjection X x = nativeCoverProjection X x) :
    f = nativeCoverDeckMap g := by
  let b := nativeCoverIdentityPoint X x
  let Vf : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (op ⦋0⦌) v = x} :=
    ⟨f.app (op ⦋0⦌) b, (congrArg (fun k => k.app (op ⦋0⦌) b) hEnd).trans
      (nativeCoverProjection_identityPoint X x)⟩
  let Vg : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (op ⦋0⦌) v = x} :=
    ⟨(nativeCoverDeckMap g).app (op ⦋0⦌) b,
      (congrArg (fun k => k.app (op ⦋0⦌) b) (nativeCoverDeckMap_projection g)).trans
        (nativeCoverProjection_identityPoint X x)⟩
  have hCoordinate : nativeCoverVertexPathEquiv x Vf = nativeCoverVertexPathEquiv x Vg :=
    (nativeCover_liftedSelfHomotopy_rootCoordinate x H f K hProjection hEnd).trans
      (hTrace.trans (nativeCoverDeckMap_rootCoordinate x g).symm)
  have hPoint : f.app (op ⦋0⦌) b = (nativeCoverDeckMap g).app (op ⦋0⦌) b :=
    congrArg Subtype.val ((nativeCoverVertexPathEquiv x).injective hCoordinate)
  exact nativeCover_map_ext_at_identity x x f (nativeCoverDeckMap g)
    (hEnd.trans (nativeCoverDeckMap_projection g).symm) hPoint

/-- The genuine native fibration lift and its computed root identify a whole
identity-to-deck homotopy. Its projection is the original cylinder map. -/
theorem exists_nativeCover_deckHomotopy_of_selfTrace {X : SSet.{u}}
    [SSet.KanComplex X] (x : X _⦋0⦌) (H : SSet.Homotopy (𝟙 X) (𝟙 X))
    (g : End (SSet.FundamentalGroupoid.mk x))
    (hTrace : SSet.FundamentalGroupoid.homMk
      (SSet.Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x) = (g⁻¹).asHom) :
    ∃ K : SSet.Homotopy (𝟙 (nativeCover X x)) (nativeCoverDeckMap g),
      K.h ≫ nativeCoverProjection X x =
        (nativeCoverProjection X x ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
  obtain ⟨f, K, hProjection, hEnd⟩ := exists_nativeCover_selfHomotopy_lift x H
  have hF : f = nativeCoverDeckMap g :=
    nativeCover_liftedSelfHomotopy_endpoint_eq_deck x H g hTrace f K hProjection hEnd
  subst f
  exact ⟨K, hProjection⟩

end SSet.KanComplex
