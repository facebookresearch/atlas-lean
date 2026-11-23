/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetCoproducts

/-!
# Coproducts of Kan fibrations

A map from an actual standard simplex into a coproduct factors through
one summand. The Cartesian component square then derives the top map of
any lifting problem in that summand. Component lifting produces the actual
coproduct lift. Applying this to every positive-dimensional horn proves
closure for the pinned Kan fibration definition.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

private theorem hasLiftingProperty_sigmaMap_stdSimplex_aux
    {ι : Type u} {A B : ι → SSet.{u}} (q : ∀ c, A c ⟶ B c)
    {X : SSet.{u}} {n : ℕ} (i : X ⟶ (Δ[n] : SSet.{u}))
    (hq : ∀ c, HasLiftingProperty i (q c)) :
    HasLiftingProperty i (Limits.Sigma.map q) where
  sq_hasLift {top bottom} hsq := by
    obtain ⟨c, β, hβ⟩ := exists_sigma_ι_comp_eq bottom
    let sq := isPullback_sigma_ι_sigmaMap q c
    have hw : top ≫ Limits.Sigma.map q = (i ≫ β) ≫ Sigma.ι B c := by
      rw [Category.assoc, hβ]
      exact hsq.w
    let top' : X ⟶ A c := sq.lift top (i ≫ β) hw
    have h1 : top' ≫ Sigma.ι A c = top := sq.lift_fst _ _ _
    have h2 : top' ≫ q c = i ≫ β := sq.lift_snd _ _ _
    let _ : HasLiftingProperty i (q c) := hq c
    let component : CommSq top' i (q c) β := CommSq.mk h2
    refine CommSq.HasLift.mk' ⟨component.lift ≫ Sigma.ι A c, ?_, ?_⟩
    · rw [← Category.assoc, component.fac_left, h1]
    · rw [Category.assoc, sq.w, ← Category.assoc, component.fac_right, hβ]

/-- Component lifting gives lifting against the actual coproduct map
whenever the left map has a standard-simplex codomain. -/
theorem hasLiftingProperty_sigmaMap_stdSimplex
    {ι : Type u} {A B : ι → SSet.{u}} (q : ∀ c, A c ⟶ B c)
    {X : SSet.{u}} {n : ℕ} (i : X ⟶ (Δ[n] : SSet.{u}))
    (hq : ∀ c, HasLiftingProperty i (q c)) :
    HasLiftingProperty i (Limits.Sigma.map q) :=
  hasLiftingProperty_sigmaMap_stdSimplex_aux q i hq

private theorem fibration_sigmaMap_aux
    {ι : Type u} {A B : ι → SSet.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) : Fibration (Limits.Sigma.map q) := by
  rw [modelCategoryQuillen.fibration_iff]
  intro X Y i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  apply hasLiftingProperty_sigmaMap_stdSimplex q (horn (n + 1) k).ι
  intro c
  exact (modelCategoryQuillen.fibration_iff (q c)).mp (hq c) _ (horn_ι_mem_J (n + 1) k)

/-- An arbitrary coproduct of actual Kan fibrations is a Kan fibration. -/
theorem fibration_sigmaMap
    {ι : Type u} {A B : ι → SSet.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) : Fibration (Limits.Sigma.map q) :=
  fibration_sigmaMap_aux q hq

end SSet
