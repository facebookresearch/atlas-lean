/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction

/-!
# Certificates for the native universal cover

Packages the native cover of a connected Kan complex with its fibration, path
fibres, unique simplex lifts and deck transformations. The projection induces
isomorphisms on higher homotopy groups at every covering vertex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet.KanComplex

/-- The first projection of the original native pullback is a Kan fibration. -/
theorem nativeCoverProjection_fibration (X : SSet.{u}) (x : X _⦋0⦌) :
    HomotopicalAlgebra.Fibration (nativeCoverProjection X x) := by
  let : Groupoid.{u} (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)) :=
    Groupoid.ofIsGroupoid
  let : HomotopicalAlgebra.Fibration (nativeCoverNerveProjection X x) := by
    dsimp only [nativeCoverNerveProjection]
    exact CategoryTheory.nerve.fibration_nerveMap_of_isIsofibration
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x))
  dsimp only [nativeCoverProjection]
  exact SSet.fibration_pullback_fst

end SSet.KanComplex

namespace SSet.KanComplex

private theorem nativeCoverPiMap_bijective_target_eq
    {A B : SSet.{u}} (f : A ⟶ B) (a : A _⦋0⦌) (t : B _⦋0⦌)
    (h : f.app (Opposite.op ⦋0⦌) a = t) (n : ℕ) :
    Function.Bijective (π.map (x := a) f h n) =
      Function.Bijective (π.map (x := a) f rfl n) := by
  cases h
  rfl

/-- The original projection is bijective on higher homotopy at every original cover vertex. -/
theorem nativeCoverProjection_piMap_bijective_atVertex
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (v : (nativeCover X x) _⦋0⦌) {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective (π.map (x := v) (nativeCoverProjection X x) rfl n) := by
  let P : SSet.{u} := nativeCover X x
  let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
  let p : P ⟶ X := nativeCoverProjection X x
  let : KanComplex P := nativeCover_kanComplex X x
  have hb : p.app (Opposite.op ⦋0⦌) b = x := nativeCoverProjection_identityPoint X x
  have hB : Function.Bijective (π.map (x := b) p hb n) :=
    nativeCoverProjection_piMap_bijective (X := X) (x := x) (n := n) hn
  let f0 : π n P b → π n X (p.app (Opposite.op ⦋0⦌) b) := π.map (x := b) p rfl n
  let fv : π n P v → π n X (p.app (Opposite.op ⦋0⦌) v) := π.map (x := v) p rfl n
  have h0 : Function.Bijective f0 :=
    Eq.mp (nativeCoverPiMap_bijective_target_eq p b x hb n) hB
  obtain ⟨e⟩ := nativeCover_exists_edge_from_identityPoint (X := X) (x := x) v
  let g : SSet.FundamentalGroupoid.mk (X := P) b ⟶
      SSet.FundamentalGroupoid.mk (X := P) v := SSet.FundamentalGroupoid.homMk e
  let EP : π n P b ≃ π n P v := π.actionEquiv (X := P) (n := n) g
  let EX : π n X (p.app (Opposite.op ⦋0⦌) b) ≃
      π n X (p.app (Opposite.op ⦋0⦌) v) :=
    π.actionEquiv (X := X) (n := n) ((SSet.mapFundamentalGroupoid p).map g)
  have hcomm (a : π n P b) : fv (EP a) = EX (f0 a) := by
    have hEP : EP a = π.action (X := P) (n := n) g a :=
      π.actionEquiv_apply (X := P) (n := n) g a
    have hEX : EX (f0 a) =
        π.action (X := X) (n := n) ((SSet.mapFundamentalGroupoid p).map g) (f0 a) :=
      π.actionEquiv_apply (X := X) (n := n) ((SSet.mapFundamentalGroupoid p).map g) (f0 a)
    exact (congrArg fv hEP).trans
      ((π.action_naturality (n := n) p g a).trans hEX.symm)
  have hF : fv = fun a => EX (f0 (EP.symm a)) := by
    funext a
    exact (congrArg fv (EP.apply_symm_apply a)).symm.trans (hcomm (EP.symm a))
  have hbij : Function.Bijective (fun a => EX (f0 (EP.symm a))) :=
    EX.bijective.comp (h0.comp EP.symm.bijective)
  change Function.Bijective fv
  rw [hF]
  exact hbij

attribute [local instance] nativeCover_kanComplex

/-- The same original projection gives the actual higher group equivalence at each vertex. -/
noncomputable def nativeCoverProjectionPiMulEquivAtVertex
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (v : (nativeCover X x) _⦋0⦌) (k : ℕ) (hk : 1 ≤ k) :
    π (k + 1) (nativeCover X x) v ≃*
      π (k + 1) X ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v) :=
  MulEquiv.ofBijective
    (π.mapHom (x := v) (nativeCoverProjection X x) rfl k)
    (nativeCoverProjection_piMap_bijective_atVertex x v (Nat.succ_le_succ hk))

/-- Deprecated alias for `nativeCoverProjectionPiMulEquivAtVertex`. -/
@[deprecated nativeCoverProjectionPiMulEquivAtVertex (since := "2026-10-28"),
  nolint defsWithUnderscore]
alias nativeCoverProjection_piMulEquiv_atVertex := nativeCoverProjectionPiMulEquivAtVertex

/-- The constructed all-vertex group equivalence uses exactly the original native map. -/
@[simp]
theorem nativeCoverProjectionPiMulEquivAtVertex_apply
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (v : (nativeCover X x) _⦋0⦌) (k : ℕ) (hk : 1 ≤ k)
    (a : π (k + 1) (nativeCover X x) v) :
    nativeCoverProjectionPiMulEquivAtVertex x v k hk a =
      π.map (x := v) (nativeCoverProjection X x) rfl (k + 1) a := rfl

/-- Deprecated alias for `nativeCoverProjectionPiMulEquivAtVertex_apply`. -/
@[deprecated nativeCoverProjectionPiMulEquivAtVertex_apply (since := "2026-10-28")]
alias nativeCoverProjection_piMulEquiv_atVertex_apply :=
  nativeCoverProjectionPiMulEquivAtVertex_apply

end SSet.KanComplex

namespace SSet.KanComplex

attribute [local instance] nativeCover_kanComplex

private theorem nativeUniversalCover_square {X : SSet.{u}} {x : X _⦋0⦌} :
    nativeCoverProjection X x ≫ nativeCoverUnit X =
      nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x := by
  dsimp only [nativeCover, nativeCoverProjection, nativeCoverUnderProjection] at *
  exact Limits.pullback.condition

/-- All carriers and maps in this certificate are the original native constructions. -/
structure NativeUniversalCoverData (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) where
  kan : KanComplex (nativeCover X x)
  projection_fibration : HomotopicalAlgebra.Fibration (nativeCoverProjection X x)
  square : nativeCoverProjection X x ≫ nativeCoverUnit X =
    nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x
  point_projection : (nativeCoverProjection X x).app (Opposite.op ⦋0⦌)
    (nativeCoverIdentityPoint X x) = x
  point_underProjection : (nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌)
    (nativeCoverIdentityPoint X x) =
      ComposableArrows.mk₀ (CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x)))
  connected : (nativeCover X x).IsConnected
  piOne_subsingleton : ∀ v : (nativeCover X x) _⦋0⦌,
    Subsingleton (π 1 (nativeCover X x) v)
  /-- For each vertex `z`, the fiber of the projection over `z` is identified with the
  constant simplicial set on the fundamental-groupoid paths `x ⟶ z`. -/
  path_fiber : ∀ z : X _⦋0⦌,
    ((Functor.const SimplexCategoryᵒᵖ).obj
      (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z)) ≅
        (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u})
  /-- Lifts a fundamental-groupoid path `x ⟶ z` to a vertex of the cover over `z`. -/
  vertex_lift : ∀ z : X _⦋0⦌,
    (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) →
      {v : (nativeCover X x) _⦋0⦌ //
        (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  vertex_path : ∀ z γ, nativeCoverVertexPathEquiv z (vertex_lift z γ) = γ
  first_lift_unique : ∀ (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (v : (nativeCover X x) _⦋0⦌)
    (_ : (SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ =
      (SSet.const ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v) :
        (Δ[0] : SSet.{u}) ⟶ X)),
    ∃! L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x,
      L ≫ nativeCoverProjection X x = σ ∧
        (SSet.yonedaEquiv.symm
          (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
            (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ L =
              (SSet.const v : (Δ[0] : SSet.{u}) ⟶ nativeCover X x)
  projection_surjective : ∀ n : ℕ,
    Function.Surjective ((nativeCoverProjection X x).app (Opposite.op ⦋n⦌))
  vertex_fiber_nonempty : ∀ z : X _⦋0⦌,
    Nonempty {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  /-- The deck transformation of the cover attached to each loop at `x`, an endomorphism
  of `x` in the fundamental groupoid. -/
  deck_iso : End (SSet.FundamentalGroupoid.mk x) → (nativeCover X x ≅ nativeCover X x)
  deck_projection : ∀ g, (deck_iso g).hom ≫ nativeCoverProjection X x =
    nativeCoverProjection X x
  deck_underProjection : ∀ g, (deck_iso g).hom ≫ nativeCoverUnderProjection X x =
    nativeCoverUnderProjection X x ≫
      CategoryTheory.nerveMap (CategoryTheory.Under.map (g⁻¹).asHom)
  deck_one : (deck_iso 1).hom = 𝟙 (nativeCover X x)
  deck_mul : ∀ g h, (deck_iso (g * h)).hom = (deck_iso h).hom ≫ (deck_iso g).hom
  /-- The action of `π 1 X x` on the `n`-simplices of the cover. -/
  simplex_action : ∀ n : ℕ, MulAction (π 1 X x) ((nativeCover X x) _⦋n⦌)
  simplex_action_deck : ∀ n (a : π 1 X x) (s : (nativeCover X x) _⦋n⦌),
    letI := simplex_action n
    a • s = (nativeCoverDeckMap (piOneMulEquivFundamentalGroupoidEnd x a)).app
      (Opposite.op ⦋n⦌) s
  simplex_action_naturality : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a : π 1 X x) (s : (nativeCover X x) _⦋n⦌),
    letI := simplex_action n
    letI := simplex_action m
    (nativeCover X x).map θ.op (a • s) = a • ((nativeCover X x).map θ.op s)
  simplex_action_projection : ∀ n (a : π 1 X x) (s : (nativeCover X x) _⦋n⦌),
    letI := simplex_action n
    (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) (a • s) =
      (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) s
  higher_pi_bijective : ∀ (n : ℕ) (_ : 2 ≤ n) (v : (nativeCover X x) _⦋0⦌),
    Function.Bijective (π.map (x := v) (nativeCoverProjection X x) rfl n)
  /-- For `k ≥ 1` and each vertex `v` of the cover, a group isomorphism from `π (k + 1)` of
  the cover at `v` to `π (k + 1)` of `X` at the image of `v`. -/
  higher_pi_group : ∀ (k : ℕ) (_ : 1 ≤ k) (v : (nativeCover X x) _⦋0⦌),
    π (k + 1) (nativeCover X x) v ≃*
      π (k + 1) X ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v)
  higher_pi_group_apply : ∀ k hk v (a : π (k + 1) (nativeCover X x) v),
    higher_pi_group k hk v a =
      π.map (x := v) (nativeCoverProjection X x) rfl (k + 1) a

attribute [nolint defsWithUnderscore] NativeUniversalCoverData.path_fiber
  NativeUniversalCoverData.vertex_lift NativeUniversalCoverData.deck_iso
  NativeUniversalCoverData.simplex_action NativeUniversalCoverData.higher_pi_group

/-- Construct the original universal-cover data without any supplied covering result. -/
noncomputable def nativeUniversalCover
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    NativeUniversalCoverData X x where
  kan := nativeCover_kanComplex X x
  projection_fibration := nativeCoverProjection_fibration X x
  square := (by exact nativeUniversalCover_square)
  point_projection := nativeCoverProjection_identityPoint X x
  point_underProjection := nativeCoverUnderProjection_identityPoint X x
  connected := nativeCover_isConnected (X := X) (x := x)
  piOne_subsingleton := (nativeCover_isConnected_and_piOne_subsingleton (X := X) (x := x)).2
  path_fiber := nativeCoverFiberPathIso (X := X) (x := x)
  vertex_lift z γ := (nativeCoverVertexPathEquiv (X := X) (x := x) z).symm γ
  vertex_path z γ := (nativeCoverVertexPathEquiv (X := X) (x := x) z).apply_symm_apply γ
  first_lift_unique n σ v hv := existsUnique_nativeCoverSimplexLiftFromFirst σ v hv
  projection_surjective := nativeCoverProjection_app_surjective x
  vertex_fiber_nonempty := nativeCover_vertexFiber_nonempty (X := X) (x := x)
  deck_iso := nativeCoverDeckIso (X := X) (x := x)
  deck_projection g := by
    rw [nativeCoverDeckIso_hom]
    exact nativeCoverDeckMap_projection g
  deck_underProjection g := by
    rw [nativeCoverDeckIso_hom]
    exact nativeCoverDeckMap_underProjection g
  deck_one := (nativeCoverDeckIso_hom (1 : End (SSet.FundamentalGroupoid.mk x))).trans
    (nativeCoverDeckMap_one (X := X) (x := x))
  deck_mul g h := by
    rw [nativeCoverDeckIso_hom, nativeCoverDeckIso_hom, nativeCoverDeckIso_hom]
    exact nativeCoverDeckMap_mul g h
  simplex_action := nativeCoverPiOneSimplexAction x
  simplex_action_deck _ _ _ := rfl
  simplex_action_naturality := nativeCoverPiOneSimplexAction_naturality x
  simplex_action_projection := nativeCoverPiOneSimplexAction_projection x
  higher_pi_bijective n hn v := nativeCoverProjection_piMap_bijective_atVertex x v hn
  higher_pi_group k hk v := nativeCoverProjectionPiMulEquivAtVertex x v k hk
  higher_pi_group_apply k hk v a := nativeCoverProjectionPiMulEquivAtVertex_apply x v k hk a

end SSet.KanComplex

end
