/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.GlueAux
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.GlueData.MkCore

universe u

private theorem resLE_id_self (Y : Scheme.{u}) (W : Y.Opens) (e : W ≤ (𝟙 Y) ⁻¹ᵁ W) :
    Scheme.Hom.resLE (𝟙 Y) W W e = 𝟙 _ := by
  rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, Category.id_comp, Category.comp_id]

/-- Gluing data that glues `J` copies of `X` along all of `X` by identities. -/
private noncomputable abbrev diagonalCore (X : Scheme.{u}) (J : Type u) :
    Scheme.GlueData.MkCore.{u} where
  J := J
  U _ := X
  V _ _ := ⊤
  t _ _ := 𝟙 _
  V_id _ := rfl
  t_id _ := rfl
  t_inter _ _ _ := le_rfl
  cocycle _ _ _ := (congrArg (· ≫ _) (resLE_id_self _ _ _)).trans (Category.id_comp _)

/-- With identity transition maps, the gluing condition identifies all charts. -/
private theorem diagonalCore_ι_eq (X : Scheme.{u}) (J : Type u) (i j : J) :
    (diagonalCore X J).glueData.ι i = (diagonalCore X J).glueData.ι j := by
  have : IsIso (⊤ : X.Opens).ι := (Scheme.topIso X).isIso_hom
  refine (cancel_epi (⊤ : X.Opens).ι).1 ?_
  simpa using ((diagonalCore X J).t_ι_ι i j).symm

-- Gluing copies of `X` along identities gives `X` back: every chart is an isomorphism.
example (X : Scheme.{u}) (J : Type u) (i : J) : IsIso ((diagonalCore X J).glueData.ι i) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  obtain ⟨j, x, rfl⟩ := (diagonalCore X J).glueData.ι_jointly_surjective y
  exact ⟨x, by rw [diagonalCore_ι_eq X J i j]; exact rfl⟩

-- The preimage of one chart's image under another is the open the data prescribes.
example (X : Scheme.{u}) (J : Type u) (i j : J) :
    (diagonalCore X J).glueData.ι i ⁻¹ᵁ ((diagonalCore X J).glueData.ι j).opensRange = ⊤ :=
  (diagonalCore X J).preimage_opensRange i j
