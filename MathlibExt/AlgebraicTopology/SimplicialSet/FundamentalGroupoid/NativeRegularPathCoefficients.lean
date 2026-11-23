/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore

/-!
# Regular path coefficients for native covers

Relates lifted simplices in the native cover to vertex lifts and paths in the
fundamental groupoid, and describes their transport under ordinal maps.
Constructs regular coefficient functors on free abelian groups of these paths,
including the pullback version.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace SSet.KanComplex

/-- A lift of the original simplex is exactly a vertex over its first vertex. -/
def nativeCoverSimplexFiberVertexEquiv
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x //
      L ≫ nativeCoverProjection X x = σ} ≃
    {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v =
        (SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
          ((SSet.yonedaEquiv.symm
            (SSet.stdSimplex.obj₀Equiv.symm
              (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
                (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ)} := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))
  let z : X _⦋0⦌ := (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (α ≫ σ)
  change {L : (Δ[n] : SSet.{u}) ⟶ P // L ≫ p = σ} ≃
    {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z}
  let vertex :
      {L : (Δ[n] : SSet.{u}) ⟶ P // L ≫ p = σ} →
        {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z} :=
    fun L => ⟨(SSet.yonedaEquiv (X := P) (n := ⦋0⦌)) (α ≫ L.val), by
      have hp : (α ≫ L.val) ≫ p = α ≫ σ :=
        (Category.assoc α L.val p).trans
          (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => α ≫ f) L.property)
      exact (SSet.yonedaEquiv_comp (α ≫ L.val) p).symm.trans
        (congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) hp)⟩
  let liftVertex :
      {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z} →
        {L : (Δ[n] : SSet.{u}) ⟶ P // L ≫ p = σ} :=
    fun v => by
      have hv : α ≫ σ =
          (SSet.const (p.app (Opposite.op ⦋0⦌) v.val) : (Δ[0] : SSet.{u}) ⟶ X) :=
        (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).injective
          (v.property.symm.trans
            (SSet.yonedaEquiv_const (p.app (Opposite.op ⦋0⦌) v.val)).symm)
      exact ⟨nativeCoverSimplexLiftFromFirstMap σ v.val hv,
        nativeCoverSimplexLiftFromFirstMap_projection σ v.val hv⟩
  refine { toFun := vertex, invFun := liftVertex, left_inv := ?_, right_inv := ?_ }
  · intro L
    apply Subtype.ext
    let v : P _⦋0⦌ := (vertex L).val
    have hv : α ≫ σ =
        (SSet.const (p.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ X) :=
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).injective
        ((vertex L).property.symm.trans
          (SSet.yonedaEquiv_const (p.app (Opposite.op ⦋0⦌) v)).symm)
    have hfirst : α ≫ L.val = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) :=
      ((SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm_apply_apply (α ≫ L.val)).symm.trans
        (SSet.yonedaEquiv_symm_zero v)
    obtain ⟨W, _, hUnique⟩ := existsUnique_nativeCoverSimplexLiftFromFirst σ v hv
    have hcanon : nativeCoverSimplexLiftFromFirstMap σ v hv = L.val :=
      (hUnique (nativeCoverSimplexLiftFromFirstMap σ v hv)
        ⟨nativeCoverSimplexLiftFromFirstMap_projection σ v hv,
          nativeCoverSimplexLiftFromFirstMap_firstVertex σ v hv⟩).trans
        (hUnique L.val ⟨L.property, hfirst⟩).symm
    exact hcanon
  · intro v
    apply Subtype.ext
    have hv : α ≫ σ =
        (SSet.const (p.app (Opposite.op ⦋0⦌) v.val) : (Δ[0] : SSet.{u}) ⟶ X) :=
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).injective
        (v.property.symm.trans
          (SSet.yonedaEquiv_const (p.app (Opposite.op ⦋0⦌) v.val)).symm)
    exact (congrArg (SSet.yonedaEquiv (X := P) (n := ⦋0⦌))
      (nativeCoverSimplexLiftFromFirstMap_firstVertex σ v.val hv)).trans
        (SSet.yonedaEquiv_const v.val)

/-- The coordinate is the actual first vertex of the original lifted simplex. -/
theorem nativeCoverSimplexFiberVertexEquiv_apply
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x //
      L ≫ nativeCoverProjection X x = σ}) :
    (nativeCoverSimplexFiberVertexEquiv σ L).val =
      (SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm
          (SSet.stdSimplex.obj₀Equiv.symm
            (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
              (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ L.val) := rfl

/-- Lifts of the original simplex are its actual first-vertex path classes. -/
def nativeCoverSimplexFiberPathEquiv
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x //
      L ≫ nativeCoverProjection X x = σ} ≃
    (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm
          (SSet.stdSimplex.obj₀Equiv.symm
            (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
              (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ))) :=
  (nativeCoverSimplexFiberVertexEquiv σ).trans (nativeCoverVertexPathEquiv _)

/-- The path coordinate uses the proved original vertex-path identification. -/
theorem nativeCoverSimplexFiberPathEquiv_apply
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x //
      L ≫ nativeCoverProjection X x = σ}) :
    nativeCoverSimplexFiberPathEquiv σ L =
      nativeCoverVertexPathEquiv _ (nativeCoverSimplexFiberVertexEquiv σ L) := rfl


/-- Original simplices in the actual pulled-back cover retain their target lift. -/
def nativeCoverPullbackSimplexFiberEquiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ} ≃
    {T : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y //
      T ≫ nativeCoverProjection Y y = σ ≫ f} := by
  let P : SSet.{u} := nativeCover Y y
  let p : P ⟶ Y := nativeCoverProjection Y y
  let W : SSet.{u} := pullback f p
  let q : W ⟶ X := pullback.fst f p
  let r : W ⟶ P := pullback.snd f p
  change {L : (Δ[n] : SSet.{u}) ⟶ W // L ≫ q = σ} ≃
    {T : (Δ[n] : SSet.{u}) ⟶ P // T ≫ p = σ ≫ f}
  let forward :
      {L : (Δ[n] : SSet.{u}) ⟶ W // L ≫ q = σ} →
        {T : (Δ[n] : SSet.{u}) ⟶ P // T ≫ p = σ ≫ f} :=
    fun L => ⟨L.val ≫ r, by
      have hs : q ≫ f = r ≫ p := pullback.condition
      exact (Category.assoc L.val r p).trans
        ((congrArg (fun h : W ⟶ Y => L.val ≫ h) hs.symm).trans
          ((Category.assoc L.val q f).symm.trans
            (congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ X => h ≫ f) L.property)))⟩
  let backward :
      {T : (Δ[n] : SSet.{u}) ⟶ P // T ≫ p = σ ≫ f} →
        {L : (Δ[n] : SSet.{u}) ⟶ W // L ≫ q = σ} :=
    fun T => ⟨pullback.lift σ T.val T.property.symm,
      pullback.lift_fst σ T.val T.property.symm⟩
  refine { toFun := forward, invFun := backward, left_inv := ?_, right_inv := ?_ }
  · intro L
    apply Subtype.ext
    have hc : σ ≫ f = (L.val ≫ r) ≫ p := (forward L).property.symm
    have hq : pullback.lift σ (L.val ≫ r) hc ≫ q = σ :=
      pullback.lift_fst σ (L.val ≫ r) hc
    have hr : pullback.lift σ (L.val ≫ r) hc ≫ r = L.val ≫ r :=
      pullback.lift_snd σ (L.val ≫ r) hc
    exact pullback.hom_ext (hq.trans L.property.symm) hr
  · intro T
    apply Subtype.ext
    exact pullback.lift_snd σ T.val T.property.symm

/-- The comparison uses the actual second projection of the unchanged pullback. -/
theorem nativeCoverPullbackSimplexFiberEquiv_apply
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ}) :
    (nativeCoverPullbackSimplexFiberEquiv f y σ L).val =
      L.val ≫ pullback.snd f (nativeCoverProjection Y y) := rfl

/-- Pullback-cover coordinates use paths in the original target groupoid. -/
def nativeCoverPullbackSimplexPathEquiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    {L : (Δ[n] : SSet.{u}) ⟶ pullback f (nativeCoverProjection Y y) //
      L ≫ pullback.fst f (nativeCoverProjection Y y) = σ} ≃
    (SSet.FundamentalGroupoid.mk y ⟶ SSet.FundamentalGroupoid.mk
      ((SSet.yonedaEquiv (X := Y) (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm
          (SSet.stdSimplex.obj₀Equiv.symm
            (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
              (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ (σ ≫ f)))) :=
  (nativeCoverPullbackSimplexFiberEquiv f y σ).trans
    (nativeCoverSimplexFiberPathEquiv (σ ≫ f))

end SSet.KanComplex

namespace SSet.KanComplex

private theorem nativePathNerve_firstObject
    {C : Type u} [Category.{u} C] {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ CategoryTheory.nerve C) :
    (SSet.yonedaEquiv f).obj (0 : Fin (n + 1)) =
      CategoryTheory.nerveEquiv ((SSet.yonedaEquiv (n := ⦋0⦌))
        ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
          (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ f)) := by
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ (0 : Fin (n + 1))
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  have hi : (SSet.stdSimplex.map θ : (Δ[0] : SSet.{u}) ⟶ Δ[n]) = α :=
    (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)).eq_symm_apply.mpr
      ((SSet.yonedaEquiv_map θ).trans
        (show SSet.stdSimplex.objEquiv.symm θ =
          SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)) from rfl))
  have hn := SSet.yonedaEquiv_naturality θ f
  have ho : CategoryTheory.nerveEquiv
      ((CategoryTheory.nerve C).map θ.op (SSet.yonedaEquiv f)) =
      (SSet.yonedaEquiv f).obj (0 : Fin (n + 1)) := rfl
  exact ho.symm.trans (congrArg (CategoryTheory.nerveEquiv (C := C))
    (hn.trans (congrArg (SSet.yonedaEquiv (X := CategoryTheory.nerve C) (n := ⦋0⦌))
      (congrArg (fun a : (Δ[0] : SSet.{u}) ⟶ Δ[n] => a ≫ f) hi))))

/-- The unit's first object is the original first vertex, with its literal endpoint. -/
theorem nativeCoverUnitChain_firstVertex_eq
    {X : SSet.{u}} {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)).obj (0 : Fin (n + 1)) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ)) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let η : X ⟶ CategoryTheory.nerve Γ := nativeCoverUnit X
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let z : X _⦋0⦌ := (SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ)
  have hη : η.app (Opposite.op ⦋0⦌) z =
      (CategoryTheory.nerveEquiv (C := Γ)).symm (SSet.FundamentalGroupoid.mk z) := by
    dsimp only [η, nativeCoverUnit]
    exact SSet.fundamentalGroupoidNerveEquiv_app_zero X Γ (𝟭 Γ) z
  have hs : (SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ (σ ≫ η)) =
      η.app (Opposite.op ⦋0⦌) z :=
    (congrArg (SSet.yonedaEquiv (X := CategoryTheory.nerve Γ) (n := ⦋0⦌))
      (Category.assoc α σ η).symm).trans (SSet.yonedaEquiv_comp (α ≫ σ) η)
  exact (nativePathNerve_firstObject (σ ≫ η)).trans
    ((congrArg (CategoryTheory.nerveEquiv (C := Γ)) (hs.trans hη)).trans
      ((CategoryTheory.nerveEquiv (C := Γ)).apply_symm_apply _))

/-- Reindexing computes the new endpoint from the original unit simplex. -/
theorem nativeCoverUnitChain_restrictedFirst_eq
    {X : SSet.{u}} {m n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
    (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)).obj
        (θ.toOrderHom (0 : Fin (m + 1))) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌))
        (α ≫ (SSet.stdSimplex.map θ ≫ σ))) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let η : X ⟶ CategoryTheory.nerve Γ := nativeCoverUnit X
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ η)
  let T' : ComposableArrows Γ m := SSet.yonedaEquiv ((SSet.stdSimplex.map θ ≫ σ) ≫ η)
  have ht : (CategoryTheory.nerve Γ).map θ.op T = T' :=
    (SSet.yonedaEquiv_naturality θ (σ ≫ η)).trans
      (congrArg (SSet.yonedaEquiv (X := CategoryTheory.nerve Γ) (n := ⦋m⦌))
        (Category.assoc (SSet.stdSimplex.map θ) σ η).symm)
  have ho : ((CategoryTheory.nerve Γ).map θ.op T).obj (0 : Fin (m + 1)) =
      T.obj (θ.toOrderHom (0 : Fin (m + 1))) := rfl
  exact ho.symm.trans ((congrArg
    (fun K : ComposableArrows Γ m => K.obj (0 : Fin (m + 1))) ht).trans
      (nativeCoverUnitChain_firstVertex_eq (SSet.stdSimplex.map θ ≫ σ)))

/-- The actual base path traversed when a restriction changes the first vertex. -/
def nativeCoverSimplexPathTransport
    {X : SSet.{u}} {m n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
    (SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ σ)) ⟶
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌))
        (αm ≫ (SSet.stdSimplex.map θ ≫ σ)))) :=
  eqToHom (nativeCoverUnitChain_firstVertex_eq σ).symm ≫
    (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)).map
      (homOfLE (Fin.zero_le (θ.toOrderHom (0 : Fin (m + 1))))) ≫
    eqToHom (nativeCoverUnitChain_restrictedFirst_eq σ θ)

private theorem nativePathRestriction_square {X : SSet.{u}} {x : X _⦋0⦌} :
    nativeCoverProjection X x ≫ nativeCoverUnit X =
      nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x := by
  dsimp only [nativeCoverProjection, nativeCoverUnderProjection]
  exact pullback.condition

private theorem nativePathUnder_transport
    {C : Type u} [Category.{u} C] {y : C} {n : ℕ}
    (τ : ComposableArrows (CategoryTheory.Under y) n) (T : ComposableArrows C n)
    (hp : τ ⋙ CategoryTheory.Under.forget y = T) (j : Fin (n + 1))
    {z₀ z₁ : C} (κ₀ : T.obj (0 : Fin (n + 1)) = z₀) (κ₁ : T.obj j = z₁) :
    (τ.obj j).hom ≫ eqToHom ((CategoryTheory.Functor.congr_obj hp j).trans κ₁) =
      ((τ.obj (0 : Fin (n + 1))).hom ≫
        eqToHom ((CategoryTheory.Functor.congr_obj hp (0 : Fin (n + 1))).trans κ₀)) ≫
      (eqToHom κ₀.symm ≫ T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κ₁) := by
  have hw := CategoryTheory.Under.w (τ.map (homOfLE (Fin.zero_le j)))
  have hf := CategoryTheory.Functor.congr_hom hp (homOfLE (Fin.zero_le j))
  change (τ.map (homOfLE (Fin.zero_le j))).right = _ at hf
  rw [← hw, hf]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- Restriction follows the original Under triangle and the computed base path. -/
theorem nativeCoverSimplexFiberPathEquiv_restrict
    {X : SSet.{u}} {x : X _⦋0⦌} {m n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x //
      L ≫ nativeCoverProjection X x = σ}) :
    nativeCoverSimplexFiberPathEquiv (SSet.stdSimplex.map θ ≫ σ)
        ⟨SSet.stdSimplex.map θ ≫ L.val, (Category.assoc _ _ _).trans
          (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => SSet.stdSimplex.map θ ≫ f)
            L.property)⟩ =
      nativeCoverSimplexFiberPathEquiv σ L ≫ nativeCoverSimplexPathTransport σ θ := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let Y : SSet.{u} := CategoryTheory.nerve Γ
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let q : A ⟶ Y := nativeCoverNerveProjection X x
  let σ' : (Δ[m] : SSet.{u}) ⟶ X := SSet.stdSimplex.map θ ≫ σ
  let L' : {f : (Δ[m] : SSet.{u}) ⟶ P // f ≫ p = σ'} :=
    ⟨SSet.stdSimplex.map θ ≫ L.val, (Category.assoc _ _ _).trans
      (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => SSet.stdSimplex.map θ ≫ f) L.property)⟩
  let τ : ComposableArrows (CategoryTheory.Under y) n := SSet.yonedaEquiv (L.val ≫ r)
  let τ' : ComposableArrows (CategoryTheory.Under y) m := SSet.yonedaEquiv (L'.val ≫ r)
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ η)
  let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
  let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let z₀ : X _⦋0⦌ := (SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ σ)
  let z₁ : X _⦋0⦌ := (SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ σ')
  let V₀ := nativeCoverSimplexFiberVertexEquiv σ L
  let V₁ := nativeCoverSimplexFiberVertexEquiv σ' L'
  let W₀ : Type u := {U : CategoryTheory.Under y // U.right = SSet.FundamentalGroupoid.mk z₀}
  let W₁ : Type u := {U : CategoryTheory.Under y // U.right = SSet.FundamentalGroupoid.mk z₁}
  let U₀ : W₀ := nativeCoverVertexUnderEquiv z₀ V₀
  let U₁ : W₁ := nativeCoverVertexUnderEquiv z₁ V₁
  have hfirst {k : ℕ} (f : (Δ[k] : SSet.{u}) ⟶ P) :
      (SSet.yonedaEquiv (f ≫ r)).obj (0 : Fin (k + 1)) =
        CategoryTheory.nerveEquiv (r.app (Opposite.op ⦋0⦌)
          ((SSet.yonedaEquiv (n := ⦋0⦌))
            ((SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
              (0 : Fin (k + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[k]) ≫ f))) := by
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[k] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (k + 1)))
    exact (nativePathNerve_firstObject (f ≫ r)).trans
      (congrArg (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
        ((congrArg (SSet.yonedaEquiv (X := A) (n := ⦋0⦌))
          (Category.assoc α f r).symm).trans (SSet.yonedaEquiv_comp (α ≫ f) r)))
  have hθ : A.map θ.op τ = τ' :=
    (SSet.yonedaEquiv_naturality θ (L.val ≫ r)).trans
      (congrArg (SSet.yonedaEquiv (X := A) (n := ⦋m⦌))
        (Category.assoc (SSet.stdSimplex.map θ) L.val r).symm)
  have hτ : τ'.obj (0 : Fin (m + 1)) = τ.obj j :=
    (congrArg (fun K : ComposableArrows (CategoryTheory.Under y) m =>
      K.obj (0 : Fin (m + 1))) hθ).symm.trans (show (A.map θ.op τ).obj _ = τ.obj j from rfl)
  have hU₀ : U₀.val = τ.obj (0 : Fin (n + 1)) := by
    have hu : U₀.val = CategoryTheory.nerveEquiv (r.app (Opposite.op ⦋0⦌) V₀.val) := by
      dsimp only [U₀, nativeCoverVertexUnderEquiv, r] ; rfl
    exact hu.trans ((congrArg (fun v : P _⦋0⦌ => CategoryTheory.nerveEquiv
      (r.app (Opposite.op ⦋0⦌) v)) (nativeCoverSimplexFiberVertexEquiv_apply σ L)).trans
        (hfirst L.val).symm)
  have hU₁ : U₁.val = τ.obj j := by
    have hu : U₁.val = CategoryTheory.nerveEquiv (r.app (Opposite.op ⦋0⦌) V₁.val) := by
      dsimp only [U₁, nativeCoverVertexUnderEquiv, r] ; rfl
    exact (hu.trans ((congrArg (fun v : P _⦋0⦌ => CategoryTheory.nerveEquiv
      (r.app (Opposite.op ⦋0⦌) v)) (nativeCoverSimplexFiberVertexEquiv_apply σ' L')).trans
        (hfirst L'.val).symm)).trans hτ
  have hp : τ ⋙ CategoryTheory.Under.forget y = T := by
    have hc : p ≫ η = r ≫ q := nativePathRestriction_square
    have hm : (L.val ≫ r) ≫ q = σ ≫ η :=
      (Category.assoc L.val r q).trans
        ((congrArg (fun f : P ⟶ Y => L.val ≫ f) hc.symm).trans
          ((Category.assoc L.val p η).symm.trans
            (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => f ≫ η) L.property)))
    change q.app (Opposite.op ⦋n⦌) τ = T
    exact (SSet.yonedaEquiv_comp (L.val ≫ r) q).symm.trans
      (congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)) hm)
  let κ₀ : T.obj (0 : Fin (n + 1)) = SSet.FundamentalGroupoid.mk z₀ :=
    nativeCoverUnitChain_firstVertex_eq σ
  let κ₁ : T.obj j = SSet.FundamentalGroupoid.mk z₁ :=
    nativeCoverUnitChain_restrictedFirst_eq σ θ
  have e₀ : U₀ = ⟨τ.obj (0 : Fin (n + 1)),
      (CategoryTheory.Functor.congr_obj hp (0 : Fin (n + 1))).trans κ₀⟩ := Subtype.ext hU₀
  have e₁ : U₁ = ⟨τ.obj j, (CategoryTheory.Functor.congr_obj hp j).trans κ₁⟩ := Subtype.ext hU₁
  have hφ₀ : nativeCoverSimplexFiberPathEquiv σ L =
      (τ.obj (0 : Fin (n + 1))).hom ≫
        eqToHom ((CategoryTheory.Functor.congr_obj hp (0 : Fin (n + 1))).trans κ₀) :=
    (nativeCoverSimplexFiberPathEquiv_apply σ L).trans
      ((nativeCoverVertexPathEquiv_apply z₀ V₀).trans
        (congrArg (fun U : W₀ => U.val.hom ≫ eqToHom U.property) e₀))
  have hφ₁ : nativeCoverSimplexFiberPathEquiv σ' L' =
      (τ.obj j).hom ≫ eqToHom ((CategoryTheory.Functor.congr_obj hp j).trans κ₁) :=
    (nativeCoverSimplexFiberPathEquiv_apply σ' L').trans
      ((nativeCoverVertexPathEquiv_apply z₁ V₁).trans
        (congrArg (fun U : W₁ => U.val.hom ≫ eqToHom U.property) e₁))
  change nativeCoverSimplexFiberPathEquiv σ' L' =
    nativeCoverSimplexFiberPathEquiv σ L ≫ nativeCoverSimplexPathTransport σ θ
  rw [hφ₁, hφ₀]
  exact nativePathUnder_transport τ T hp j κ₀ κ₁

end SSet.KanComplex

namespace SSet.KanComplex

private theorem nativePathTransport_chainReindex
    {X : SSet.{u}} {m n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.yonedaEquiv ((SSet.stdSimplex.map θ ≫ σ) ≫ nativeCoverUnit X) :
        ComposableArrows (SSet.FundamentalGroupoid X) m) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ SSet.yonedaEquiv (σ ≫ nativeCoverUnit X) := by
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let T : ComposableArrows (SSet.FundamentalGroupoid X) n :=
    SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)
  let S : ComposableArrows (SSet.FundamentalGroupoid X) m :=
    SSet.yonedaEquiv ((SSet.stdSimplex.map θ ≫ σ) ≫ nativeCoverUnit X)
  change S = Y.map θ.op T
  exact ((SSet.yonedaEquiv_naturality θ (σ ≫ nativeCoverUnit X)).trans
    (congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋m⦌))
      (Category.assoc (SSet.stdSimplex.map θ) σ (nativeCoverUnit X)).symm)).symm

private theorem nativePathTransport_chain_id
    {C : Type u} [Category.{u} C] {n : ℕ} (T : ComposableArrows C n)
    {a b : C} (κa : T.obj (0 : Fin (n + 1)) = a)
    (κb : T.obj (0 : Fin (n + 1)) = b) (e : b = a) :
    (eqToHom κa.symm ≫ T.map (𝟙 (0 : Fin (n + 1))) ≫ eqToHom κb) ≫ eqToHom e = 𝟙 a := by
  rw [T.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

private theorem nativePathTransport_chain_comp
    {C : Type u} [Category.{u} C] {l m n : ℕ}
    (T : ComposableArrows C n) (S : ComposableArrows C m)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (ρ : ⦋l⦌ ⟶ ⦋m⦌)
    (he : S = (SimplexCategory.toCat.map θ).toFunctor ⋙ T)
    {a b c d : C} (κa : T.obj (0 : Fin (n + 1)) = a)
    (κb : T.obj (θ.toOrderHom (0 : Fin (m + 1))) = b)
    (κb' : S.obj (0 : Fin (m + 1)) = b)
    (κc : S.obj (ρ.toOrderHom (0 : Fin (l + 1))) = c) (e : c = d)
    (κd : T.obj (θ.toOrderHom (ρ.toOrderHom (0 : Fin (l + 1)))) = d) :
    ((eqToHom κa.symm ≫ T.map (homOfLE (Fin.zero_le (θ.toOrderHom (0 : Fin (m + 1))))) ≫
          eqToHom κb) ≫
      (eqToHom κb'.symm ≫ S.map (homOfLE (Fin.zero_le (ρ.toOrderHom (0 : Fin (l + 1))))) ≫
          eqToHom κc)) ≫ eqToHom e =
      eqToHom κa.symm ≫ T.map
        (homOfLE (Fin.zero_le (θ.toOrderHom (ρ.toOrderHom (0 : Fin (l + 1)))))) ≫ eqToHom κd := by
  let F : Fin (m + 1) ⥤ Fin (n + 1) := (SimplexCategory.toCat.map θ).toFunctor
  change S = F ⋙ T at he
  subst S
  let j : Fin (n + 1) := θ.toOrderHom (0 : Fin (m + 1))
  let k : Fin (m + 1) := ρ.toOrderHom (0 : Fin (l + 1))
  let i : Fin (n + 1) := θ.toOrderHom k
  let g : j ⟶ i := homOfLE (θ.toOrderHom.monotone (Fin.zero_le k))
  change T.obj j = b at κb'
  change T.obj i = c at κc
  change ((eqToHom κa.symm ≫ T.map (homOfLE (Fin.zero_le j)) ≫ eqToHom κb) ≫
      (eqToHom κb'.symm ≫ T.map g ≫ eqToHom κc)) ≫ eqToHom e =
    eqToHom κa.symm ≫ T.map (homOfLE (Fin.zero_le i)) ≫ eqToHom κd
  have hmid : eqToHom κb ≫ eqToHom κb'.symm = 𝟙 (T.obj j) :=
    (eqToHom_trans κb κb'.symm).trans (eqToHom_refl (T.obj j) (κb.trans κb'.symm))
  have htail : eqToHom κc ≫ eqToHom e = eqToHom κd :=
    (eqToHom_trans κc e).trans (show eqToHom (κc.trans e) = eqToHom κd from rfl)
  have hmaps : T.map (homOfLE (Fin.zero_le j)) ≫
      T.map g = T.map (homOfLE (Fin.zero_le i)) :=
    (T.map_comp (homOfLE (Fin.zero_le j)) g).symm.trans
      (congrArg (fun f : (0 : Fin (n + 1)) ⟶ i => T.map f) (Subsingleton.elim _ _))
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom κb) (eqToHom κb'.symm)
      (T.map g ≫ eqToHom κc ≫ eqToHom e),
    hmid, Category.id_comp, htail]
  simpa only [Category.assoc] using
    congrArg (fun f : T.obj (0 : Fin (n + 1)) ⟶ T.obj i => eqToHom κa.symm ≫ f ≫ eqToHom κd) hmaps

/-- Identity restriction transports along the actual equality of first vertices. -/
theorem nativeCoverSimplexPathTransport_id
    {X : SSet.{u}} {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
    let hσ : SSet.stdSimplex.map (𝟙 ⦋n⦌) ≫ σ = σ :=
      (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n] => f ≫ σ)
        (SSet.stdSimplex.map_id ⦋n⦌)).trans (Category.id_comp σ)
    nativeCoverSimplexPathTransport σ (𝟙 ⦋n⦌) ≫ eqToHom
        (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X =>
          SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ f))) hσ) =
      𝟙 (SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ))) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let σ' : (Δ[n] : SSet.{u}) ⟶ X := SSet.stdSimplex.map (𝟙 ⦋n⦌) ≫ σ
  let hσ : σ' = σ := (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n] => f ≫ σ)
    (SSet.stdSimplex.map_id ⦋n⦌)).trans (Category.id_comp σ)
  let e : SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ')) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ)) :=
    congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X =>
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ f))) hσ
  let κa : T.obj (0 : Fin (n + 1)) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ)) :=
    nativeCoverUnitChain_firstVertex_eq σ
  let κb : T.obj (0 : Fin (n + 1)) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ σ')) :=
    nativeCoverUnitChain_restrictedFirst_eq σ (𝟙 ⦋n⦌)
  change (eqToHom κa.symm ≫ T.map (𝟙 (0 : Fin (n + 1))) ≫ eqToHom κb) ≫ eqToHom e = _
  exact nativePathTransport_chain_id T κa κb e

/-- Composed restrictions follow the same original unit path, retaining endpoint transport. -/
theorem nativeCoverSimplexPathTransport_comp
    {X : SSet.{u}} {l m n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (ρ : ⦋l⦌ ⟶ ⦋m⦌) :
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[l] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (l + 1)))
    let hσ : SSet.stdSimplex.map ρ ≫ (SSet.stdSimplex.map θ ≫ σ) =
        SSet.stdSimplex.map (ρ ≫ θ) ≫ σ :=
      (Category.assoc (SSet.stdSimplex.map ρ) (SSet.stdSimplex.map θ) σ).symm.trans
        (congrArg (fun f : (Δ[l] : SSet.{u}) ⟶ Δ[n] => f ≫ σ)
          (SSet.stdSimplex.map_comp ρ θ).symm)
    (nativeCoverSimplexPathTransport σ θ ≫
      nativeCoverSimplexPathTransport (SSet.stdSimplex.map θ ≫ σ) ρ) ≫ eqToHom
        (congrArg (fun f : (Δ[l] : SSet.{u}) ⟶ X =>
          SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (α ≫ f))) hσ) =
      nativeCoverSimplexPathTransport σ (ρ ≫ θ) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let σ₁ : (Δ[m] : SSet.{u}) ⟶ X := SSet.stdSimplex.map θ ≫ σ
  let σ₂ : (Δ[l] : SSet.{u}) ⟶ X := SSet.stdSimplex.map ρ ≫ σ₁
  let σc : (Δ[l] : SSet.{u}) ⟶ X := SSet.stdSimplex.map (ρ ≫ θ) ≫ σ
  let αn : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let αm : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (m + 1)))
  let αl : (Δ[0] : SSet.{u}) ⟶ Δ[l] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (l + 1)))
  let hσ : σ₂ = σc :=
    (Category.assoc (SSet.stdSimplex.map ρ) (SSet.stdSimplex.map θ) σ).symm.trans
      (congrArg (fun f : (Δ[l] : SSet.{u}) ⟶ Δ[n] => f ≫ σ) (SSet.stdSimplex.map_comp ρ θ).symm)
  let e : SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αl ≫ σ₂)) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αl ≫ σc)) :=
    congrArg (fun f : (Δ[l] : SSet.{u}) ⟶ X =>
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αl ≫ f))) hσ
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)
  let S : ComposableArrows Γ m := SSet.yonedaEquiv (σ₁ ≫ nativeCoverUnit X)
  let κa : T.obj (0 : Fin (n + 1)) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αn ≫ σ)) :=
    nativeCoverUnitChain_firstVertex_eq σ
  let κb : T.obj (θ.toOrderHom (0 : Fin (m + 1))) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ σ₁)) :=
    nativeCoverUnitChain_restrictedFirst_eq σ θ
  let κb' : S.obj (0 : Fin (m + 1)) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αm ≫ σ₁)) :=
    nativeCoverUnitChain_firstVertex_eq σ₁
  let κc : S.obj (ρ.toOrderHom (0 : Fin (l + 1))) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αl ≫ σ₂)) :=
    nativeCoverUnitChain_restrictedFirst_eq σ₁ ρ
  let κd : T.obj (θ.toOrderHom (ρ.toOrderHom (0 : Fin (l + 1)))) =
      SSet.FundamentalGroupoid.mk ((SSet.yonedaEquiv (n := ⦋0⦌)) (αl ≫ σc)) :=
    nativeCoverUnitChain_restrictedFirst_eq σ (ρ ≫ θ)
  change ((eqToHom κa.symm ≫ T.map (homOfLE (Fin.zero_le (θ.toOrderHom (0 : Fin (m + 1))))) ≫
      eqToHom κb) ≫
    (eqToHom κb'.symm ≫ S.map (homOfLE (Fin.zero_le (ρ.toOrderHom (0 : Fin (l + 1))))) ≫
      eqToHom κc)) ≫ eqToHom e =
    eqToHom κa.symm ≫ T.map
      (homOfLE (Fin.zero_le (θ.toOrderHom (ρ.toOrderHom (0 : Fin (l + 1)))))) ≫ eqToHom κd
  exact nativePathTransport_chain_comp T S θ ρ (nativePathTransport_chainReindex σ θ)
    κa κb κb' κc e κd

end SSet.KanComplex

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

/-- The regular path coefficient transports its basis by original postcomposition. -/
def regularPathCoefficientTransport (y : C) {z z' : C} (f : z ⟶ z') :
    FreeAbelianGroup (y ⟶ z) →+ FreeAbelianGroup (y ⟶ z') :=
  FreeAbelianGroup.map (fun γ => γ ≫ f)

/-- Transport sends the generator for a path to the generator for its composite. -/
theorem regularPathCoefficientTransport_of (y : C) {z z' : C} (f : z ⟶ z')
    (γ : y ⟶ z) :
    regularPathCoefficientTransport y f (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ f) := rfl

/-- Identity paths act by the actual identity additive homomorphism. -/
theorem regularPathCoefficientTransport_id (y z : C) :
    regularPathCoefficientTransport y (𝟙 z) =
      AddMonoidHom.id (FreeAbelianGroup (y ⟶ z)) := by
  change FreeAbelianGroup.map (fun γ : y ⟶ z => γ ≫ 𝟙 z) = _
  calc
    _ = FreeAbelianGroup.map id :=
      congrArg FreeAbelianGroup.map (funext fun γ => Category.comp_id γ)
    _ = _ := FreeAbelianGroup.map_id

/-- Consecutive path transports compose in the original covariant order. -/
theorem regularPathCoefficientTransport_comp (y : C) {z z' z'' : C}
    (f : z ⟶ z') (g : z' ⟶ z'') :
    regularPathCoefficientTransport y (f ≫ g) =
      (regularPathCoefficientTransport y g).comp (regularPathCoefficientTransport y f) := by
  change FreeAbelianGroup.map (fun γ : y ⟶ z => γ ≫ (f ≫ g)) = _
  calc
    _ = FreeAbelianGroup.map ((fun δ : y ⟶ z' => δ ≫ g) ∘
        (fun γ : y ⟶ z => γ ≫ f)) :=
      congrArg FreeAbelianGroup.map (funext fun γ => (Category.assoc γ f g).symm)
    _ = _ := FreeAbelianGroup.map_comp

/-- Free abelian path coefficients form a functor using the proved transport laws. -/
def regularPathCoefficientFunctor (y : C) : C ⥤ AddCommGrpCat.{v} where
  obj z := AddCommGrpCat.of (FreeAbelianGroup (y ⟶ z))
  map f := AddCommGrpCat.ofHom (regularPathCoefficientTransport y f)
  map_id z := by
    apply AddCommGrpCat.hom_ext
    exact regularPathCoefficientTransport_id y z
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact regularPathCoefficientTransport_comp y f g

/-- The bundled coefficient functor retains the original path generator formula. -/
theorem regularPathCoefficientFunctor_map_of (y : C) {z z' : C}
    (f : z ⟶ z') (γ : y ⟶ z) :
    (regularPathCoefficientFunctor y).map f (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ f) := rfl

end Category

section Groupoid

variable {C : Type u} [Groupoid.{v} C]

/-- The inverse original path supplies the inverse of regular coefficient transport. -/
def regularPathCoefficientTransportEquiv (y : C) {z z' : C} (f : z ⟶ z') :
    FreeAbelianGroup (y ⟶ z) ≃+ FreeAbelianGroup (y ⟶ z') :=
  FreeAbelianGroup.equivOfEquiv
    { toFun := fun γ => γ ≫ f
      invFun := fun δ => δ ≫ Groupoid.inv f
      left_inv := fun γ => by simp [Category.assoc]
      right_inv := fun δ => by simp [Category.assoc] }

/-- The derived transport equivalence has the same forward coefficient map. -/
theorem regularPathCoefficientTransportEquiv_apply (y : C) {z z' : C}
    (f : z ⟶ z') (a : FreeAbelianGroup (y ⟶ z)) :
    regularPathCoefficientTransportEquiv y f a =
      regularPathCoefficientTransport y f a := rfl

end Groupoid

end CategoryTheory

namespace SSet.KanComplex

/-- Regular integral coefficients use paths in the actual fundamental groupoid. -/
def nativeRegularCoefficientFunctor {X : SSet.{u}} (x : X _⦋0⦌) :
    SSet.FundamentalGroupoid X ⥤ AddCommGrpCat.{u} :=
  regularPathCoefficientFunctor (SSet.FundamentalGroupoid.mk x)

/-- Native regular transport is original fundamental-groupoid postcomposition. -/
theorem nativeRegularCoefficientFunctor_map_of {X : SSet.{u}} (x : X _⦋0⦌)
    {z z' : SSet.FundamentalGroupoid X} (f : z ⟶ z')
    (γ : SSet.FundamentalGroupoid.mk x ⟶ z) :
    (nativeRegularCoefficientFunctor x).map f (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ f) := rfl

/-- An original simplicial map pulls back the target's regular coefficients. -/
def nativePullbackRegularCoefficientFunctor {X Y : SSet.{u}}
    (f : X ⟶ Y) (y : Y _⦋0⦌) :
    SSet.FundamentalGroupoid X ⥤ AddCommGrpCat.{u} :=
  SSet.mapFundamentalGroupoid f ⋙ nativeRegularCoefficientFunctor y

/-- Pullback transport keeps paths in the target and the actual induced arrow. -/
theorem nativePullbackRegularCoefficientFunctor_map_of {X Y : SSet.{u}}
    (f : X ⟶ Y) (y : Y _⦋0⦌) {z z' : SSet.FundamentalGroupoid X}
    (g : z ⟶ z')
    (γ : SSet.FundamentalGroupoid.mk y ⟶ (SSet.mapFundamentalGroupoid f).obj z) :
    (nativePullbackRegularCoefficientFunctor f y).map g (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ (SSet.mapFundamentalGroupoid f).map g) := rfl

end SSet.KanComplex

end
