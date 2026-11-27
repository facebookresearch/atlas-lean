/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.SimplexTriviality

/-!
# Fixed-fiber presentations over simplices in a connected base

Let p:E→B be a minimal simplicial fibration, with B connected, and choose a vertex b₀ of B. For
every simplex map σ:Δ[n]→B, the pullback projection E ×_B Δ[n]→Δ[n] is a trivial bundle with the
fixed strict fiber over b₀.

The fiber is the pullback of p along the vertex map Δ[0]→B representing b₀. The product
presentation commutes with the pullback projection to Δ[n]. All objects and maps are in an
arbitrary simplicial-set universe u.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial SSet MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.MinimalFibration

/-- Let p:E→B be a minimal Kan fibration over a connected simplicial set B, and b₀ a chosen vertex.
For every σ:Δ[n]→B, its pullback projection has a product presentation over Δ[n] with fixed
fiber E ×_B Δ[0] over b₀. -/
noncomputable def trivialBundleWithFiber_pullback_stdSimplex
    {E B : SSet.{u}} (p : E ⟶ B) (hp : IsMinimalFibration p)
    [B.IsConnected] (b₀ : B _⦋0⦌)
    {n : ℕ} (σ : Δ[n] ⟶ B) :
    CategoryTheory.TrivialBundleWithFiber
      (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
      (pullback.snd p σ) := by
  let v₀ : (Δ[n] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))
  let first : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const v₀
  let q : pullback p σ ⟶ Δ[n] := pullback.snd p σ
  have hpq : IsMinimalFibration q := isMinimalFibration_pullback_snd p σ hp
  let hσ := trivialBundleWithFiber_stdSimplex q hpq
  let bσv : B _⦋0⦌ := σ.app _ v₀
  let bσ : (Δ[0] : SSet.{u}) ⟶ B := SSet.const bσv
  have hfirst : first ≫ σ = bσ := by
    simp [first, bσ, bσv, v₀]
  have sqNestedRaw : IsPullback
      (pullback.fst q first ≫ pullback.fst p σ)
      (pullback.snd q first) p (first ≫ σ) := by
    simpa only [q] using
      (IsPullback.of_hasPullback q first).paste_horiz
        (IsPullback.of_hasPullback p σ)
  have sqNested : IsPullback
      (pullback.fst q first ≫ pullback.fst p σ)
      (pullback.snd q first) p bσ := by
    simpa only [hfirst] using sqNestedRaw
  have hcomp : Relation.EqvGen π₀Rel b₀ bσv :=
    (π₀.mk_eq_mk_iff b₀ bσv).mp (Subsingleton.elim _ _)
  let componentIsoOfEqvGen : ∀ {x y : B _⦋0⦌},
      Relation.EqvGen π₀Rel x y →
      ∃ e : pullback p (SSet.const (X := (Δ[0] : SSet.{u})) x) ≅
          pullback p (SSet.const (X := (Δ[0] : SSet.{u})) y),
        e.hom ≫ pullback.snd p
            (SSet.const (X := (Δ[0] : SSet.{u})) y) =
          pullback.snd p
            (SSet.const (X := (Δ[0] : SSet.{u})) x) := by
    intro x y h
    induction h with
    | rel x y hxy =>
        obtain ⟨e⟩ := hxy
        let H : SSet.Homotopy
            (SSet.const (X := (Δ[0] : SSet.{u})) x)
            (SSet.const (X := (Δ[0] : SSet.{u})) y) :=
          { h := (SSet.stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom ≫
              SSet.yonedaEquiv.symm e.edge
            h₀ := by
              simp [SSet.ι₀_stdSimplex_zero_assoc,
                SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
            h₁ := by
              simp [SSet.ι₁_stdSimplex_zero_assoc,
                SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
            rel := by
              ext m z
              rcases z with ⟨⟨a, ha⟩, t⟩
              cases ha }
        exact exists_iso_pullback_of_homotopy p hp H
          (IsPullback.of_hasPullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) x))
          (IsPullback.of_hasPullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) y))
    | refl x =>
        exact ⟨Iso.refl _, by simp⟩
    | symm _ _ _ ih =>
        obtain ⟨e, he⟩ := ih
        refine ⟨e.symm, ?_⟩
        calc
          e.inv ≫ pullback.snd p
              (SSet.const (X := (Δ[0] : SSet.{u})) _) =
            e.inv ≫ (e.hom ≫ pullback.snd p
              (SSet.const (X := (Δ[0] : SSet.{u})) _)) := by
                rw [he]
          _ = pullback.snd p
              (SSet.const (X := (Δ[0] : SSet.{u})) _) := by simp
    | trans _ _ _ _ _ ih₁ ih₂ =>
        obtain ⟨e₁, he₁⟩ := ih₁
        obtain ⟨e₂, he₂⟩ := ih₂
        refine ⟨e₁.trans e₂, ?_⟩
        simp only [Iso.trans_hom, Category.assoc, he₂, he₁]
  let componentIsoData := componentIsoOfEqvGen hcomp
  let componentIso :
      pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀) ≅
        pullback p bσ := componentIsoData.choose
  let sqCanonical : IsPullback
      (pullback.fst p bσ) (pullback.snd p bσ) p bσ :=
    IsPullback.of_hasPullback p bσ
  let nestedIso : pullback p bσ ≅ pullback q first :=
    sqCanonical.isoIsPullback E (Δ[0] : SSet.{u}) sqNested
  let fiberIso := componentIso.trans nestedIso
  simpa only [q, first, v₀] using hσ.mapFiber fiberIso

end SSet.MinimalFibration
