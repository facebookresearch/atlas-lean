/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Remark33
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Special right horns in pre-fibrant simplicial sets

Fix the horn `σ₀` in the pre-fibrant set `X`. Write `v` for the
vertex at which the `0`-th face is constant — so vertices
`1, …, n + 2` of the horn are all `v` — and `x` for its `0`-th
vertex. Write `H = Homᴸ_X(x, v)`. Under Stevenson's §2.4
description (`SSet.mappingSpaceLeft.simplexEquivSuccStd` of
`Remark33.lean`) an `m`-simplex of `H` is an
`(m + 1)`-simplex of `X` with `0`-th vertex `x` and back face
`δ₀` constant at `v`, and the `a`-th face in `H` is the
`(a + 1)`-th face in `X`. The argument has four steps; only
Step 1 uses pre-fibrancy, and it uses exactly
Definition 3.1(ii).

The remaining case `n = 0` needs no pre-fibrancy at all, in any
simplicial set: if `e` is the `1`-face (the edge `x → v`) then
`s₁e` has `0`-face `s₀v` (the constant `0`-th face, using the
horn compatibility identifying the target of `e` with `v`) and
`1`-face `e`. This is §1 below.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X : SSet.{u}}

/-!
## §0. Edges with one-sided homotopy inverses are equivalences

In any simplicial set, if every edge has a `CompStruct` right
inverse (a `2`-simplex witnessing `e ≫ g = id` in the homotopy
category), then every edge is an equivalence: this is the
usual argument in the homotopy category, where every morphism
having a right inverse implies every morphism is an
isomorphism. No horn filling in dimension `≥ 3` is involved;
`SSet.Edge.toHoHom_comp` and `SSet.Edge.toHoHom_id` are the
`2`-truncated composition relations.
-/

namespace Edge

/-- If every edge of a simplicial set admits a `CompStruct`
right inverse (a `2`-simplex witnessing its composite with a
backward edge as the identity in the homotopy category), then
every edge is an equivalence: its backward edge also has a
right inverse `h`, and in the homotopy category
`[h] = ([e] ≫ [g]) ≫ [h] = [e]`, so `[g] ≫ [e] = [g] ≫ [h]`
is the identity too. -/
theorem IsEquivalence.of_forall_exists_compStruct_id {Y : SSet.{u}}
    (h : ∀ {a b : Y _⦋0⦌} (e : Edge a b),
      ∃ g : Edge b a, Nonempty (Edge.CompStruct e g (Edge.id a)))
    {a b : Y _⦋0⦌} (e : Edge a b) : e.IsEquivalence := by
  obtain ⟨g, ⟨cg⟩⟩ := h e
  obtain ⟨hEdge, ⟨ch⟩⟩ := h g
  have hfg : e.toHoHom ≫ g.toHoHom =
      𝟙 (HomotopyCategory.mk a : hoFunctor.obj Y) := by
    rw [toHoHom_comp cg, toHoHom_id]
  have hgh : g.toHoHom ≫ hEdge.toHoHom =
      𝟙 (HomotopyCategory.mk b : hoFunctor.obj Y) := by
    rw [toHoHom_comp ch, toHoHom_id]
  have hhe : hEdge.toHoHom = e.toHoHom := by
    calc hEdge.toHoHom
        = 𝟙 (HomotopyCategory.mk a : hoFunctor.obj Y) ≫
            hEdge.toHoHom :=
          (Category.id_comp _).symm
      _ = (e.toHoHom ≫ g.toHoHom) ≫ hEdge.toHoHom := by
          rw [hfg]
      _ = e.toHoHom ≫ (g.toHoHom ≫ hEdge.toHoHom) :=
          Category.assoc _ _ _
      _ = e.toHoHom ≫ 𝟙 (HomotopyCategory.mk b : hoFunctor.obj Y) := by
          rw [hgh]
      _ = e.toHoHom := Category.comp_id _
  have hgf : g.toHoHom ≫ e.toHoHom =
      𝟙 (HomotopyCategory.mk b : hoFunctor.obj Y) := by
    rw [← hhe]; exact hgh
  exact ⟨⟨g.toHoHom, hfg, hgf⟩⟩

end Edge

/-!
## §1. The two-dimensional case holds in any simplicial set

A right outer horn `Λ[2, 2] ⟶ X` whose `0`-th face is constant
at `v` is filled by `s₁` of its `1`-face: no pre-fibrancy, and
indeed no hypothesis on `X`, is needed. This disposes of the
case `n = 0` of the main theorem, where the transported horn
in the mapping space would be one-dimensional.
-/

/-- The `0`-face of the `1`-degeneracy of a `1`-simplex is the
`0`-degeneracy of its `0`-face. -/
private lemma δ_zero_σ_one {Y : SSet.{u}} (s : Y _⦋1⦌) :
    Y.δ (0 : Fin 3) (Y.σ (1 : Fin 2) s) =
      Y.σ (0 : Fin 1) (Y.δ (0 : Fin 2) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_le Y
  -- Porting note: was `(0 : Fin 2) ≤ Fin.castSucc (0 : Fin 1)`
  -- in the the supporting result copy; now checked against the pinned Mathlib by
  -- `decide`.
    (show (0 : Fin 2) ≤ Fin.castSucc (0 : Fin 1) by decide)) s

/-- The `1`-face of the `1`-degeneracy of a `1`-simplex is the
simplex itself. -/
private lemma δ_one_σ_one {Y : SSet.{u}} (s : Y _⦋1⦌) :
    Y.δ (1 : Fin 3) (Y.σ (1 : Fin 2) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' Y
    (show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from rfl)) s

/-- **Dimension two, unconditional**: in any simplicial set, a
right outer horn `Λ[2, Fin.last 2] ⟶ X` whose `0`-th face is a
constant simplex extends to `Δ[2]`, by the `1`-degeneracy of
its `1`-face. The horn compatibility between the two faces
identifies the target of the `1`-face with the constant vertex,
so the `0`-face of the degeneracy is the prescribed constant
edge. -/
theorem exists_fill_horn_two_last_of_isConstant_hornFaceZero
    (σ₀ : (Λ[2, Fin.last 2] : SSet.{u}) ⟶ X)
    (hconst : IsConstantSimplex
      (hornFaceZero σ₀
        (show (0 : Fin 3) ≠ Fin.last 2 from by decide))) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ X,
      σ₀ = Λ[2, Fin.last 2].ι ≫ σ := by
  set s₁₂ := σ₀.app _ (horn.face (Fin.last 2) 0 (by decide)) with hs₁₂
  set s₀₂ := σ₀.app _ (horn.face (Fin.last 2) 1 (by decide)) with hs₀₂
  have hcompat : X.δ (0 : Fin 2) s₀₂ = X.δ (0 : Fin 2) s₁₂ := by
    have hf₀ : horn.ι (Fin.last 2) 0 (by decide) ≫ σ₀ =
        yonedaEquiv.symm s₁₂ := by
      rw [horn.ι, yonedaEquiv_symm_comp, hs₁₂]
    have hf₁ : horn.ι (Fin.last 2) 1 (by decide) ≫ σ₀ =
        yonedaEquiv.symm s₀₂ := by
      rw [horn.ι, yonedaEquiv_symm_comp, hs₀₂]
    have hc := (horn.IsCompatible.of_hom σ₀).δ_pred_comp
      (0 : Fin 3) (1 : Fin 3) (by decide) (by decide) (by decide)
    rw [hf₀, hf₁, stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm] at hc
    exact (yonedaEquiv.symm.injective hc).symm
  obtain ⟨v, hv⟩ := hconst
  have hs₁₂eq : s₁₂ = X.σ (0 : Fin 1) v := by
    have h1 : s₁₂ = constSimplex X 1 v := hv
    rw [h1, constSimplex_succ, constSimplex_zero]
  have htgt : X.δ (0 : Fin 2) s₀₂ = v := by
    rw [hcompat, hs₁₂eq]
    exact ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_σ_self' X
        (show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl)) v
  have hface0 : X.δ (0 : Fin 3) (X.σ (1 : Fin 2) s₀₂) = s₁₂ := by
    rw [δ_zero_σ_one, htgt, hs₁₂eq]
  have hface1 : X.δ (1 : Fin 3) (X.σ (1 : Fin 2) s₀₂) = s₀₂ :=
    δ_one_σ_one s₀₂
  refine ⟨yonedaEquiv.symm (X.σ (1 : Fin 2) s₀₂),
    horn.hom_ext' fun j hj ↦ ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  fin_cases j
  · exact congr_arg yonedaEquiv.symm hface0.symm
  · exact congr_arg yonedaEquiv.symm hface1.symm
  · exact absurd rfl hj

/-!
## §2. Left mapping spaces of a pre-fibrant set are quasicategories

Step 1 of the informal proof: the horn transport of
`Remark33.lean` §4, restricted to horns whose
index is not the last one. For such horns the transported
horn in `X` is inner with constant `0`-th face, so
pre-fibrancy alone fills it; the named special input of that
file is never used. The proof below follows
`SSet.kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special`
verbatim apart from the filling step and the discarded
`i = last` case.
-/

/-- **Horn transport, non-last cases**: for pre-fibrant `X`,
every compatible family of faces of a horn in
`Homᴸ_X(x, y)` whose missing index is not the last one —
inner horns and the left outer horn — is the family of faces
of a simplex of `Homᴸ_X(x, y)`. One-dimensional horns are
filled by degeneracies; in higher dimensions the family plus
the constant back face is an inner horn with constant `0`-th
face in `X`, filled by Definition 3.1(ii). -/
theorem exists_lift_mappingSpaceLeft_of_isPreFibrant_of_ne_last
    (X : SSet.{u}) [IsPreFibrant X] (x y : (Δ[0] : SSet.{u}) ⟶ X)
    ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (hi : i ≠ Fin.last (n + 1))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ mappingSpaceLeft X x y)
    (hf : horn.IsCompatible f) :
    ∃ (φ : Δ[n + 1] ⟶ mappingSpaceLeft X x y),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain _ | n := n
  · -- One-dimensional horns: fill by the degenerate edge.
    obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 2, j ≠ i := by
      by_cases hi0 : i = 0
      · exact ⟨1, by simp [hi0]⟩
      · exact ⟨0, Ne.symm hi0⟩
    have hδσ : stdSimplex.δ j₀ ≫ stdSimplex.σ (0 : Fin 1) =
        𝟙 (Δ[0] : SSet.{u}) := by
      have hσ : (stdSimplex.σ (0 : Fin 1) :
            (Δ[1] : SSet.{u}) ⟶ Δ[0]) =
          SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) := rfl
      rw [stdSimplex_δ_eq_map, hσ, ← CategoryTheory.Functor.map_comp]
      have hcomp : SimplexCategory.δ j₀ ≫
          SimplexCategory.σ (0 : Fin 1) = 𝟙 ⦋0⦌ := by
        fin_cases j₀
        · exact SimplexCategory.δ_comp_σ_self
        · exact SimplexCategory.δ_comp_σ_succ
      rw [hcomp, CategoryTheory.Functor.map_id]
    refine ⟨stdSimplex.σ 0 ≫ f j₀ hj₀, fun j hj ↦ ?_⟩
    have hji : j = j₀ := by
      have h1 : j.val < 2 := j.is_lt
      have h2 : j₀.val < 2 := j₀.is_lt
      have h3 : i.val < 2 := i.is_lt
      apply Fin.ext
      simp only [ne_eq, Fin.ext_iff] at hj hj₀
      omega
    subst hji
    rw [← Category.assoc, hδσ, Category.id_comp]
  · -- Higher-dimensional horns: transport to `X`.
    -- The transported faces `s j : Δ[n + 2] ⟶ X`.
    set s : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 2] : SSet.{u}) ⟶ X :=
      fun j hj ↦
        ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
          (yonedaEquiv (f j hj))).1 with hs
    have hsback : ∀ (j : Fin (n + 3)) (hj : j ≠ i),
        stdSimplex.δ (0 : Fin (n + 3)) ≫ s j hj =
          toDeltaZero (Δ[n + 1] : SSet.{u}) ≫ y :=
      fun j hj ↦
        ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
          (yonedaEquiv (f j hj))).2.2
    have hsvert : ∀ (j : Fin (n + 3)) (hj : j ≠ i),
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            s j hj = x :=
      fun j hj ↦
        ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
          (yonedaEquiv (f j hj))).2.1
    -- The horn in `X`: add the constant back face as face `0`.
    set g : ∀ (k : Fin (n + 4)) (_ : k ≠ i.succ),
        (Δ[n + 2] : SSet.{u}) ⟶ X := fun k hk ↦
      if hk0 : k = 0 then toDeltaZero Δ[n + 2] ≫ y
      else s (k.pred hk0)
        (fun h ↦ hk (by rw [← Fin.succ_pred k hk0, h])) with hg
    have hg_zero : ∀ (h : (0 : Fin (n + 4)) ≠ i.succ),
        g 0 h = toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ y := by
      intro h
      exact dite_eq_left rfl
    have hg_succ : ∀ (j : Fin (n + 3)) (hj : j ≠ i)
        (h : j.succ ≠ i.succ), g j.succ h = s j hj := by
      intro j hj h
      exact dite_eq_right (Fin.succ_ne_zero j)
    have hcompat : horn.IsCompatible g := by
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      by_cases hj0 : j = 0
      · -- Compatibility with the constant back face.
        subst hj0
        obtain ⟨k', rfl⟩ := k.eq_succ_of_ne_zero
          (Fin.ne_zero_of_lt hjk)
        have hk' : k' ≠ i := fun h ↦ hk (by rw [h])
        have htd : stdSimplex.δ
              ((k'.succ).pred (Fin.ne_zero_of_lt hjk)) ≫
              toDeltaZero (Δ[n + 2] : SSet.{u}) =
            toDeltaZero (Δ[n + 1] : SSet.{u}) := toDeltaZero_eq _
        have e0 : (0 : Fin (n + 4)).castPred
            (Fin.ne_last_of_lt hjk) = 0 := rfl
        rw [hg_zero, hg_succ k' hk' hk, e0, hsback k' hk',
          ← Category.assoc
            (stdSimplex.δ ((k'.succ).pred (Fin.ne_zero_of_lt hjk))),
          htd]
      · -- Compatibility of two transported faces: reduce to `hf`.
        obtain ⟨j', rfl⟩ := j.eq_succ_of_ne_zero hj0
        obtain ⟨k', rfl⟩ := k.eq_succ_of_ne_zero
          (Fin.ne_zero_of_lt hjk)
        have hj' : j' ≠ i := fun h ↦ hj (by rw [h])
        have hk' : k' ≠ i := fun h ↦ hk (by rw [h])
        have hjk' : j' < k' := Fin.succ_lt_succ_iff.mp hjk
        have hδδ : ∀ (a : Fin (n + 2)) (φ : (Δ[n + 1] : SSet.{u}) ⟶
              mappingSpaceLeft X x y),
            (mappingSpaceLeft X x y).δ a (yonedaEquiv φ) =
              yonedaEquiv (stdSimplex.δ a ≫ φ) := by
          intro a φ
          have h := stdSimplex.δ_comp_yonedaEquiv_symm
            (X := mappingSpaceLeft X x y) (i := a) (x := yonedaEquiv φ)
          rw [Equiv.symm_apply_apply] at h
          calc (mappingSpaceLeft X x y).δ a (yonedaEquiv φ)
              = yonedaEquiv (yonedaEquiv.symm
                  ((mappingSpaceLeft X x y).δ a (yonedaEquiv φ))) :=
                (Equiv.apply_symm_apply _ _).symm
            _ = yonedaEquiv (stdSimplex.δ a ≫ φ) := by rw [← h]
        have hidxL : (k'.succ).pred (Fin.ne_zero_of_lt hjk) =
            (k'.pred (Fin.ne_zero_of_lt hjk')).succ := by
          rw [Fin.pred_succ, Fin.succ_pred]
        have hidxR : (j'.succ).castPred (Fin.ne_last_of_lt hjk) =
            (j'.castPred (Fin.ne_last_of_lt hjk')).succ :=
          (Fin.succ_castPred_eq_castPred_succ
            (Fin.ne_last_of_lt hjk')).symm
        have hLHS : stdSimplex.δ
              (k'.pred (Fin.ne_zero_of_lt hjk')).succ ≫ s j' hj' =
            ((mappingSpaceLeft.simplexEquivSuccStd X x y n)
              (yonedaEquiv (stdSimplex.δ
                (k'.pred (Fin.ne_zero_of_lt hjk')) ≫
                  f j' hj'))).1 := by
          rw [show s j' hj' =
              ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
                (yonedaEquiv (f j' hj'))).1 from rfl,
            ← mappingSpaceLeft.simplexEquivSuccStd_δ X x y
              (yonedaEquiv (f j' hj'))
              (k'.pred (Fin.ne_zero_of_lt hjk')), hδδ]
        have hRHS : stdSimplex.δ
              (j'.castPred (Fin.ne_last_of_lt hjk')).succ ≫
              s k' hk' =
            ((mappingSpaceLeft.simplexEquivSuccStd X x y n)
              (yonedaEquiv (stdSimplex.δ
                (j'.castPred (Fin.ne_last_of_lt hjk')) ≫
                  f k' hk'))).1 := by
          rw [show s k' hk' =
              ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
                (yonedaEquiv (f k' hk'))).1 from rfl,
            ← mappingSpaceLeft.simplexEquivSuccStd_δ X x y
              (yonedaEquiv (f k' hk'))
              (j'.castPred (Fin.ne_last_of_lt hjk')), hδδ]
        rw [hg_succ j' hj' hj, hg_succ k' hk' hk, hidxL, hidxR,
          hLHS, hRHS]
        exact congrArg (fun τ =>
          ((mappingSpaceLeft.simplexEquivSuccStd X x y n) τ).1)
          (congrArg yonedaEquiv (hf.δ_pred_comp j' k' hj' hk' hjk'))
    -- The `0`-th face of the transported horn is constant.
    obtain ⟨σ₀, hσ₀⟩ := hcompat.exists_desc
    have hy : y = SSet.const (yonedaEquiv y) := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_const_eq, constSimplex_zero]
    have hconst : IsConstantSimplex
        (hornFaceZero σ₀ (Ne.symm (Fin.succ_ne_zero i))) := by
      rw [hornFaceZero_eq_yonedaEquiv,
        hσ₀ 0 (Ne.symm (Fin.succ_ne_zero i)), hg_zero,
        isConstantSimplex_yonedaEquiv_iff]
      refine ⟨yonedaEquiv y, ?_⟩
      calc toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ y
          = toDeltaZero (Δ[n + 2] : SSet.{u}) ≫
              SSet.const (yonedaEquiv y) :=
            congrArg (toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ ·) hy
        _ = SSet.const (yonedaEquiv y) := SSet.comp_const _ _
    -- Fill the horn in `X` by pre-fibrancy: since `i` is not
    -- the last index, `i.succ` is inner.
    have hn : i.succ < Fin.last (n + 3) := by
      have h2 : i.val ≠ n + 2 := fun h ↦ hi (Fin.ext h)
      have h1 : i.val < n + 3 := i.is_lt
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_last]
      omega
    obtain ⟨Φ, hΦ⟩ : ∃ (Φ : (Δ[n + 3] : SSet.{u}) ⟶ X),
        ∀ (k : Fin (n + 4)) (hk : k ≠ i.succ),
          stdSimplex.δ k ≫ Φ = g k hk := by
      obtain ⟨Φ, hΦeq⟩ := IsPreFibrant.hornFillingConst σ₀
        (Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero i)) hn hconst
      refine ⟨Φ, fun k hk ↦ ?_⟩
      calc stdSimplex.δ k ≫ Φ
          = horn.ι i.succ k hk ≫
              ((Λ[n + 3, i.succ] :
                  Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ) := by
            rw [← Category.assoc, horn.ι_ι]
        _ = horn.ι i.succ k hk ≫ σ₀ := by
            rw [show (Λ[n + 3, i.succ] :
                  Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ = σ₀ from
                hΦeq.symm]
        _ = g k hk := hσ₀ k hk
    -- The filler lies in the mapping space.
    have hΦback : stdSimplex.δ (0 : Fin (n + 4)) ≫ Φ =
        toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ y := by
      rw [hΦ 0 (Ne.symm (Fin.succ_ne_zero i)), hg_zero]
    have hΦvert : SSet.stdSimplex.map
          (SimplexCategory.const ⦋0⦌ ⦋n + 3⦌ 0) ≫ Φ = x := by
      obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (n + 3), j ≠ i := by
        by_cases hi0 : i = 0
        · exact ⟨1, by simp [hi0]⟩
        · exact ⟨0, Ne.symm hi0⟩
      calc SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 3⦌ 0) ≫ Φ
          = (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              stdSimplex.δ j₀.succ) ≫ Φ := by
            rw [vertexZero_comp_δ_succ]
        _ = SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              (stdSimplex.δ j₀.succ ≫ Φ) :=
            Category.assoc _ _ _
        _ = SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              s j₀ hj₀ := by
            rw [hΦ j₀.succ (by
              simp only [ne_eq, Fin.succ_inj]
              exact hj₀), hg_succ j₀ hj₀]
        _ = x := hsvert j₀ hj₀
    -- Assemble the filler in the mapping space.
    refine ⟨yonedaEquiv.symm
      ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 2)).symm
        ⟨Φ, hΦvert, hΦback⟩), fun j hj ↦ ?_⟩
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      show f j hj = yonedaEquiv.symm (yonedaEquiv (f j hj)) from
        (Equiv.symm_apply_apply _ _).symm]
    congr 1
    apply (mappingSpaceLeft.simplexEquivSuccStd X x y
      (n + 1)).injective
    apply Subtype.ext
    rw [mappingSpaceLeft.simplexEquivSuccStd_δ X x y
      ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 2)).symm
        ⟨Φ, hΦvert, hΦback⟩) j, Equiv.apply_symm_apply,
      hΦ j.succ (by
        simp only [ne_eq, Fin.succ_inj]
        exact hj), hg_succ j hj]

/-- Horn-map form of the transport: for pre-fibrant `X`, every
horn in `Homᴸ_X(x, y)` of dimension at least `2` whose missing
index is not the last one extends. In particular this covers
all inner horns and the left outer horns `Λ[n + 2, 0]`. -/
theorem exists_fill_horn_mappingSpaceLeft_of_isPreFibrant_of_ne_last
    (X : SSet.{u}) [IsPreFibrant X] (x y : (Δ[0] : SSet.{u}) ⟶ X)
    ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (hi : i ≠ Fin.last (n + 2))
    (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ mappingSpaceLeft X x y) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ mappingSpaceLeft X x y,
      σ₀ = Λ[n + 2, i].ι ≫ σ := by
  obtain ⟨φ, hφ⟩ :=
    exists_lift_mappingSpaceLeft_of_isPreFibrant_of_ne_last X x y
      hi (fun j hj ↦ horn.ι i j hj ≫ σ₀)
      (horn.IsCompatible.of_hom σ₀)
  refine ⟨φ, horn.hom_ext' fun j hj ↦ ?_⟩
  rw [← Category.assoc, horn.ι_ι]
  exact (hφ j hj).symm

/-- **Step 1**: the left mapping spaces of a pre-fibrant
simplicial set are quasicategories: inner horns of
`Homᴸ_X(x, y)` transport to inner horns with constant `0`-th
face in `X`, which fill by Definition 3.1(ii). -/
theorem quasicategory_mappingSpaceLeft_of_isPreFibrant
    (X : SSet.{u}) [IsPreFibrant X] (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    Quasicategory (mappingSpaceLeft X x y) where
  hornFilling' _ _ σ₀ _ hn :=
    exists_fill_horn_mappingSpaceLeft_of_isPreFibrant_of_ne_last
      X x y (Fin.ne_of_lt hn) σ₀

/-!
## §3. Every edge of `Homᴸ` of a pre-fibrant set is an equivalence

Step 2 of the informal proof. A `CompStruct` right inverse for
an edge `e` of `H = Homᴸ_X(x, y)` is a filler of the left outer
horn `Λ[2, 0] ⟶ H` with `1`-face the identity edge and
`2`-face `e`, supplied by §2 at `i = 0`; §0 then promotes
one-sided inverses to equivalences in the homotopy category.
-/

namespace mappingSpaceLeft

variable (X : SSet.{u}) [IsPreFibrant X]
  (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- Every edge `e` of `Homᴸ_X(x, y)`, for pre-fibrant `X`, has
a `CompStruct` right inverse: a backward edge `g` and a
`2`-simplex of the mapping space witnessing `e ≫ g = id` in
the homotopy category. The `2`-simplex is a filler of a left
outer horn `Λ[2, 0]` in the mapping space, i.e. of an inner
horn `Λ[3, 1]` with constant `0`-th face in `X`. -/
theorem exists_compStruct_id_of_isPreFibrant
    {a b : (mappingSpaceLeft X x y) _⦋0⦌}
    (e : Edge a b) :
    ∃ g : Edge b a, Nonempty (Edge.CompStruct e g (Edge.id a)) := by
  obtain ⟨φ, hφ⟩ :=
    exists_lift_mappingSpaceLeft_of_isPreFibrant_of_ne_last X x y
      (i := (0 : Fin 3)) (by decide)
      (fun j _ ↦ ![yonedaEquiv.symm e.edge,
        yonedaEquiv.symm (Edge.id a).edge,
        yonedaEquiv.symm e.edge] j)
      (by
        rw [horn.isCompatible_iff]
        intro j k hj hk hjk
        have hid : (mappingSpaceLeft X x y).δ (1 : Fin 2)
            (Edge.id a).edge = a :=
          Edge.src_eq (Edge.id a)
        have heq : (mappingSpaceLeft X x y).δ (1 : Fin 2)
            e.edge = a :=
          Edge.src_eq e
        fin_cases j <;> fin_cases k <;>
          simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk,
            Fin.reducePred, Fin.isValue, Nat.succ_eq_add_one,
            Matrix.cons_val, stdSimplex.δ_comp_yonedaEquiv_symm]
            at hjk ⊢ <;>
          simp_all)
  have hδ : ∀ (j : Fin 3) (hj : j ≠ 0),
      (mappingSpaceLeft X x y).δ j (yonedaEquiv φ) =
        ![e.edge, (Edge.id a).edge, e.edge] j := by
    intro j hj
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ j hj]
    fin_cases j
    · exact absurd rfl hj
    · simp
    · simp
  obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, c, hc⟩ :=
    Edge.CompStruct.exists_of_simplex (yonedaEquiv φ)
  have hd₂ : e₀₁.edge = e.edge := by
    rw [← c.d₂, hc]
    have h := hδ 2 (by decide)
    simpa using h
  have hd₁ : e₀₂.edge = (Edge.id a).edge := by
    rw [← c.d₁, hc]
    have h := hδ 1 (by decide)
    simpa using h
  have hx₁ : x₁ = b := by
    rw [← e₀₁.tgt_eq, hd₂, e.tgt_eq]
  have hx₂ : x₂ = a := by
    rw [← e₀₂.tgt_eq, hd₁, (Edge.id a).tgt_eq]
  exact ⟨e₁₂.ofEq hx₁ hx₂, ⟨c.ofEq hd₂ rfl hd₁⟩⟩

/-- **Step 2**: every edge of the left mapping space
`Homᴸ_X(x, y)` of a pre-fibrant simplicial set is an
equivalence in the quasicategory `Homᴸ_X(x, y)`
(§2), since every such edge has a `CompStruct` right inverse
and §0 applies. In particular the critical edge of any right
outer horn in `Homᴸ_X(x, y)` is an equivalence, so Joyal's
special outer horn filling (the supporting result) applies to it. -/
theorem edge_isEquivalence_of_isPreFibrant
    {a b : (mappingSpaceLeft X x y) _⦋0⦌}
    (e : Edge a b) : e.IsEquivalence :=
  Edge.IsEquivalence.of_forall_exists_compStruct_id
    (fun {_a _b} e' ↦
      exists_compStruct_id_of_isPreFibrant X x y e') e

end mappingSpaceLeft

/-!
## §4. The main theorem: special right horns in pre-fibrant sets

Steps 3 and 4 of the informal proof: the faces `τ₁, …, τ_{n+3}`
of the given horn in `X` are simplices of `Homᴸ_X(x, v)`
forming a right outer horn there; its critical edge is an
equivalence by §3, so the supporting result fills it in the quasicategory
`Homᴸ_X(x, v)` (§2), and the filler transports back to a
filler in `X`.
-/

/-- **the additional comparison obligation, discharged**: every
pre-fibrant simplicial set fills its special right outer
horns with constant `0`-th face. The case `n = 0` is §1
(unconditional); for `n ≥ 1` the horn is transported to a
special right outer horn in the left mapping space at its
two vertices, filled there by Joyal's theorem (§2, §3), and
transported back. -/
theorem hasSpecialRightHornFillingWithConstantZeroFace_of_isPreFibrant
    (X : SSet.{u}) [IsPreFibrant X] :
    HasSpecialRightHornFillingWithConstantZeroFace X := by
  intro n σ₀ hconst
  obtain _ | n := n
  · exact exists_fill_horn_two_last_of_isConstant_hornFaceZero
      σ₀ hconst
  · -- Now `σ₀ : Λ[n + 3, Fin.last (n + 3)] ⟶ X`; write `v` for
    -- the constant vertex and `y` for its vertex map.
    obtain ⟨v, hv⟩ := hconst
    have hface0 :
        horn.ι (Fin.last (n + 3)) 0
            (show (0 : Fin (n + 4)) ≠ Fin.last (n + 3) from by
              simp [Fin.ext_iff]) ≫ σ₀ =
          (SSet.const v : (Δ[n + 2] : SSet.{u}) ⟶ X) := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_const_eq, ← hornFaceZero_eq_yonedaEquiv]
      exact hv
    -- The `0`-th vertex map `x`, read off the `1`-face.
    set x : (Δ[0] : SSet.{u}) ⟶ X :=
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
        (horn.ι (Fin.last (n + 3)) 1
          (show (1 : Fin (n + 4)) ≠ Fin.last (n + 3) from by
            simp [Fin.ext_iff]) ≫ σ₀) with hxdef
    -- Every face other than the `0`-th has `0`-th vertex `x`:
    -- the vertex inclusion into the horn is independent of the
    -- face, since postcomposing with the (monic) horn
    -- inclusion gives the `0`-th vertex of `Δ[n + 3]`.
    have hvertex : ∀ (k : Fin (n + 4))
        (hk : k ≠ Fin.last (n + 3)) (hk0 : k ≠ 0),
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            (horn.ι (Fin.last (n + 3)) k hk ≫ σ₀) = x := by
      intro k hk hk0
      have key : ∀ (k' : Fin (n + 4)) (hk' : k' ≠ Fin.last (n + 3))
          (hk'0 : k' ≠ 0),
          (SSet.stdSimplex.map
              (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            horn.ι (Fin.last (n + 3)) k' hk') ≫
            Λ[n + 3, Fin.last (n + 3)].ι =
          SSet.stdSimplex.map
            (SimplexCategory.const ⦋0⦌ ⦋n + 3⦌ 0) := by
        intro k' hk' hk'0
        obtain ⟨j, rfl⟩ := k'.eq_succ_of_ne_zero hk'0
        rw [Category.assoc, horn.ι_ι, vertexZero_comp_δ_succ]
      have hw : SSet.stdSimplex.map
            (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            horn.ι (Fin.last (n + 3)) k hk =
          SSet.stdSimplex.map
            (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            horn.ι (Fin.last (n + 3)) 1
              (show (1 : Fin (n + 4)) ≠ Fin.last (n + 3) from by
                simp [Fin.ext_iff]) :=
        (cancel_mono Λ[n + 3, Fin.last (n + 3)].ι).mp
          ((key k hk hk0).trans
            (key 1 _ (by simp)).symm)
      calc SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              (horn.ι (Fin.last (n + 3)) k hk ≫ σ₀)
          = (SSet.stdSimplex.map
              (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            horn.ι (Fin.last (n + 3)) k hk) ≫ σ₀ :=
            (Category.assoc _ _ _).symm
        _ = x := by rw [hw]; rfl
    have hsucc_ne : ∀ (j : Fin (n + 3)),
        j ≠ Fin.last (n + 2) → j.succ ≠ Fin.last (n + 3) := by
      intro j hj h
      apply hj
      ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    -- The faces `τ_{j+1}` of `σ₀`, which will be the faces of
    -- the transported horn in the mapping space.
    set s : ∀ (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)),
        (Δ[n + 2] : SSet.{u}) ⟶ X :=
      fun j hj ↦ horn.ι (Fin.last (n + 3)) j.succ
        (hsucc_ne j hj) ≫ σ₀ with hsdef
    -- Their back faces are constant at `v`: compatibility of
    -- `σ₀` at the pair `(0, j + 1)`, with the `0`-th face
    -- constant by `hface0`.
    have hsback : ∀ (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)),
        stdSimplex.δ (0 : Fin (n + 3)) ≫ s j hj =
          toDeltaZero (Δ[n + 1] : SSet.{u}) ≫
            (SSet.const v : (Δ[0] : SSet.{u}) ⟶ X) := by
      intro j hj
      have hcomp := (horn.IsCompatible.of_hom σ₀).δ_pred_comp
        (0 : Fin (n + 4)) j.succ
        (show (0 : Fin (n + 4)) ≠ Fin.last (n + 3) from by
          simp [Fin.ext_iff])
        (hsucc_ne j hj) (Fin.succ_pos j)
      have e0 : (0 : Fin (n + 4)).castPred
          (Fin.ne_last_of_lt (Fin.succ_pos j)) = 0 := rfl
      rw [e0, hface0] at hcomp
      calc stdSimplex.δ (0 : Fin (n + 3)) ≫ s j hj
          = stdSimplex.δ
              (j.succ.pred (Fin.ne_zero_of_lt (Fin.succ_pos j))) ≫
              (SSet.const v : (Δ[n + 2] : SSet.{u}) ⟶ X) :=
            hcomp.symm
        _ = (SSet.const v : (Δ[n + 1] : SSet.{u}) ⟶ X) :=
            SSet.comp_const _ _
        _ = toDeltaZero (Δ[n + 1] : SSet.{u}) ≫
              (SSet.const v : (Δ[0] : SSet.{u}) ⟶ X) :=
            (SSet.comp_const _ _).symm
    -- The transported faces in `Homᴸ_X(x, v)`.
    set f : ∀ (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)),
        (Δ[n + 1] : SSet.{u}) ⟶
          mappingSpaceLeft X x (SSet.const v) :=
      fun j hj ↦ yonedaEquiv.symm
        ((mappingSpaceLeft.simplexEquivSuccStd X x
          (SSet.const v) (n + 1)).symm
          ⟨s j hj, hvertex j.succ (hsucc_ne j hj)
            (Fin.succ_ne_zero j), hsback j hj⟩) with hfdef
    have hfs : ∀ (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)),
        ((mappingSpaceLeft.simplexEquivSuccStd X x
          (SSet.const v) (n + 1)) (yonedaEquiv (f j hj))).1 =
          s j hj := by
      intro j hj
      have h1 : yonedaEquiv (f j hj) =
          (mappingSpaceLeft.simplexEquivSuccStd X x
            (SSet.const v) (n + 1)).symm
            ⟨s j hj, hvertex j.succ (hsucc_ne j hj)
              (Fin.succ_ne_zero j), hsback j hj⟩ := by
        simp only [hfdef, Equiv.apply_symm_apply]
      rw [h1, Equiv.apply_symm_apply]
    have hδδ : ∀ (a : Fin (n + 2))
        (φ : (Δ[n + 1] : SSet.{u}) ⟶
          mappingSpaceLeft X x (SSet.const v)),
        (mappingSpaceLeft X x (SSet.const v)).δ a
            (yonedaEquiv φ) =
          yonedaEquiv (stdSimplex.δ a ≫ φ) := by
      intro a φ
      have h := stdSimplex.δ_comp_yonedaEquiv_symm
        (X := mappingSpaceLeft X x (SSet.const v)) (i := a)
        (x := yonedaEquiv φ)
      rw [Equiv.symm_apply_apply] at h
      calc (mappingSpaceLeft X x (SSet.const v)).δ a
              (yonedaEquiv φ)
          = yonedaEquiv (yonedaEquiv.symm
              ((mappingSpaceLeft X x (SSet.const v)).δ a
                (yonedaEquiv φ))) :=
            (Equiv.apply_symm_apply _ _).symm
        _ = yonedaEquiv (stdSimplex.δ a ≫ φ) := by rw [← h]
    have hkey : ∀ (a : Fin (n + 2)) (j : Fin (n + 3))
        (hj : j ≠ Fin.last (n + 2)),
        ((mappingSpaceLeft.simplexEquivSuccStd X x
          (SSet.const v) n)
          (yonedaEquiv (stdSimplex.δ a ≫ f j hj))).1 =
          stdSimplex.δ a.succ ≫ s j hj := by
      intro a j hj
      calc ((mappingSpaceLeft.simplexEquivSuccStd X x
            (SSet.const v) n)
            (yonedaEquiv (stdSimplex.δ a ≫ f j hj))).1
          = ((mappingSpaceLeft.simplexEquivSuccStd X x
              (SSet.const v) n)
              ((mappingSpaceLeft X x (SSet.const v)).δ a
                (yonedaEquiv (f j hj)))).1 := by
            rw [hδδ]
        _ = stdSimplex.δ a.succ ≫
              ((mappingSpaceLeft.simplexEquivSuccStd X x
                (SSet.const v) (n + 1))
                (yonedaEquiv (f j hj))).1 :=
            mappingSpaceLeft.simplexEquivSuccStd_δ X x
              (SSet.const v) (yonedaEquiv (f j hj)) a
        _ = stdSimplex.δ a.succ ≫ s j hj := by rw [hfs j hj]
    -- Compatibility of the transported family: compatibility
    -- of `σ₀` at pairs `(j + 1, k + 1)`, indices shifted by one.
    have hfcompat : horn.IsCompatible f := by
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      rw [show stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫
              f j hj =
            yonedaEquiv.symm (yonedaEquiv
              (stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫
                f j hj)) from
          (Equiv.symm_apply_apply _ _).symm,
        show stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫
              f k hk =
            yonedaEquiv.symm (yonedaEquiv
              (stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫
                f k hk)) from
          (Equiv.symm_apply_apply _ _).symm]
      congr 1
      apply (mappingSpaceLeft.simplexEquivSuccStd X x
        (SSet.const v) n).injective
      apply Subtype.ext
      have hidxL : (k.succ).pred
            (Fin.ne_zero_of_lt (Fin.succ_lt_succ_iff.mpr hjk)) =
          (k.pred (Fin.ne_zero_of_lt hjk)).succ := by
        rw [Fin.pred_succ, Fin.succ_pred]
      have hidxR : (j.succ).castPred
            (Fin.ne_last_of_lt (Fin.succ_lt_succ_iff.mpr hjk)) =
          (j.castPred (Fin.ne_last_of_lt hjk)).succ :=
        (Fin.succ_castPred_eq_castPred_succ
          (Fin.ne_last_of_lt hjk)).symm
      rw [hkey (k.pred (Fin.ne_zero_of_lt hjk)) j hj,
        hkey (j.castPred (Fin.ne_last_of_lt hjk)) k hk,
        ← hidxL, ← hidxR]
      exact (horn.IsCompatible.of_hom σ₀).δ_pred_comp j.succ
        k.succ (hsucc_ne j hj) (hsucc_ne k hk)
        (Fin.succ_lt_succ_iff.mpr hjk)
    -- Fill the transported horn in the mapping space by
    -- Joyal's special outer horn filling: the mapping space
    -- is a quasicategory (§2) and the critical edge, like
    -- every edge there, is an equivalence (§3).
    obtain ⟨τ₀, hτ₀⟩ := hfcompat.exists_desc
    have hQC : Quasicategory
        (mappingSpaceLeft X x (SSet.const v)) :=
      quasicategory_mappingSpaceLeft_of_isPreFibrant X x
        (SSet.const v)
    obtain ⟨ΦH, hΦH⟩ :=
      (@hasSpecialOuterHornFilling_of_quasicategory
        (mappingSpaceLeft X x (SSet.const v)) hQC).right τ₀
        (mappingSpaceLeft.edge_isEquivalence_of_isPreFibrant X x
          (SSet.const v) (rightHornEdge τ₀))
    -- Transport the filler back to `X`.
    set Φ : (Δ[n + 3] : SSet.{u}) ⟶ X :=
      ((mappingSpaceLeft.simplexEquivSuccStd X x (SSet.const v)
        (n + 2)) (yonedaEquiv ΦH)).1 with hΦdef
    have hΦback : stdSimplex.δ (0 : Fin (n + 4)) ≫ Φ =
        toDeltaZero (Δ[n + 2] : SSet.{u}) ≫
          (SSet.const v : (Δ[0] : SSet.{u}) ⟶ X) :=
      ((mappingSpaceLeft.simplexEquivSuccStd X x (SSet.const v)
        (n + 2)) (yonedaEquiv ΦH)).2.2
    have hΦface : ∀ (j : Fin (n + 3))
        (hj : j ≠ Fin.last (n + 2)),
        stdSimplex.δ j.succ ≫ Φ = s j hj := by
      intro j hj
      have hδΦ : stdSimplex.δ j ≫ ΦH = f j hj := by
        calc stdSimplex.δ j ≫ ΦH
            = horn.ι (Fin.last (n + 2)) j hj ≫
                (Λ[n + 2, Fin.last (n + 2)].ι ≫ ΦH) := by
              rw [← Category.assoc, horn.ι_ι]
          _ = horn.ι (Fin.last (n + 2)) j hj ≫ τ₀ := by
              rw [show Λ[n + 2, Fin.last (n + 2)].ι ≫ ΦH = τ₀
                from hΦH.symm]
          _ = f j hj := hτ₀ j hj
      calc stdSimplex.δ j.succ ≫ Φ
          = ((mappingSpaceLeft.simplexEquivSuccStd X x
              (SSet.const v) (n + 1))
              (yonedaEquiv (stdSimplex.δ j ≫ ΦH))).1 := by
            rw [stdSimplex.yonedaEquiv_δ_comp,
              mappingSpaceLeft.simplexEquivSuccStd_δ X x
                (SSet.const v) (yonedaEquiv ΦH) j]
        _ = s j hj := by rw [hδΦ]; exact hfs j hj
    refine ⟨Φ, horn.hom_ext' fun k hk ↦ ?_⟩
    rw [← Category.assoc, horn.ι_ι]
    by_cases hk0 : k = 0
    · subst hk0
      rw [hface0, hΦback]
      exact (SSet.comp_const _ _).symm
    · obtain ⟨j, rfl⟩ := k.eq_succ_of_ne_zero hk0
      have hj : j ≠ Fin.last (n + 2) := by
        intro h
        apply hk
        ext
        simp only [Fin.val_succ, Fin.val_last]
        rw [show j.val = n + 2 from by
          have := congrArg Fin.val h
          simpa using this]
      rw [hΦface j hj]

/-- **Remark 3.3 for pre-fibrant simplicial sets,
unconditionally**: every left mapping space of a pre-fibrant
simplicial set is a Kan complex. This is
`SSet.kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special`
of `Remark33.lean` with its named special
right horn input discharged by
`SSet.hasSpecialRightHornFillingWithConstantZeroFace_of_isPreFibrant`. -/
theorem kanComplex_mappingSpaceLeft_of_isPreFibrant
    (X : SSet.{u}) [IsPreFibrant X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) :=
  kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special X
    (hasSpecialRightHornFillingWithConstantZeroFace_of_isPreFibrant
      X) x y

/-- Instance form of Remark 3.3 for pre-fibrant simplicial
sets, so that typeclass search finds Kan-ness of left mapping
spaces from pre-fibrancy alone. It is given low priority: for
a quasicategory the instance of
`Remark33.lean` is tried first (both prove the
same proposition `KanComplex (mappingSpaceLeft X x y)`, so
there is no diamond). -/
instance (priority := 100) (X : SSet.{u}) [IsPreFibrant X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) :=
  kanComplex_mappingSpaceLeft_of_isPreFibrant X x y

/-- **Remark 3.3 for pre-fibrant simplicial sets**, in the
exact predicate form `SSet.LeftMappingSpacesKan` consumed by
`DescentProp412.lean`: this discharges
the additional comparison obligation there ("`SSet.LeftMappingSpacesKan` of a
pre-fibrant `S`"), supplying its `LeftMappingSpacesKan S`
hypotheses (the `hKanS`/`hKanT` arguments) whenever `S` is
pre-fibrant. -/
theorem leftMappingSpacesKan_of_isPreFibrant
    (X : SSet.{u}) [IsPreFibrant X] : LeftMappingSpacesKan X :=
  leftMappingSpacesKan_of_isPreFibrant_of_special X
    (hasSpecialRightHornFillingWithConstantZeroFace_of_isPreFibrant
      X)

end SSet

end
