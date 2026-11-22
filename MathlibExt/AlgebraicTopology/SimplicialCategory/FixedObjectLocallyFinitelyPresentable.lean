/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratorCompactness
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomIsomorphismRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSmallColimits
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Genuine local finite presentability of the original fixed-label enrichment

The actual original free single-Hom standard simplices form a small
strong generator: their SAME full generator maps detect every original
Hom simplex and every original full isomorphism. Their proved finite
presentability and the genuine original all-colimit construction give
local finite presentability by the canonical strong-generator theorem.
The original object labels, full enriched Homs and coefficient universe
are retained, including empty and arbitrary label types.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable (O : Type u)

/-- The actual original free single-Hom standard simplices at every ordered pair, including loops. -/
abbrev simplexGenerator (p : O × O × ℕ) : FixedObjects O :=
  FreeSingleHom.object p.1 p.2.1 (Δ[p.2.2] : SSet.{u})

/-- The SAME actual small family of free standard-simplex enrichments. -/
abbrev simplexGenerators : ObjectProperty (FixedObjects O) := .ofObj (simplexGenerator O)

variable {O}

/-- Every actual original full map is determined by its composites with those SAME original generators. -/
theorem simplexGenerators_separating : (simplexGenerators O).IsSeparating := by
  intro C D f g h
  apply homMaps_ext
  intro x y
  ext q a
  rcases q with ⟨⟨n⟩⟩
  let k := FreeSingleHom.extend x y (Δ[n] : SSet.{u}) C (SSet.yonedaEquiv.symm a)
  have hk : k ≫ f = k ≫ g := h _ ⟨(x, y, n)⟩ k
  have hcoef := congrArg (FreeSingleHom.restrict x y (Δ[n] : SSet.{u}) D) hk
  rw [FreeSingleHom.restrict_comp, FreeSingleHom.restrict_comp,
    FreeSingleHom.restrict_extend] at hcoef
  have hv := congrArg SSet.yonedaEquiv hcoef
  have hv' : (homMap f x y).app (op ⦋n⦌) a = (homMap g x y).app (op ⦋n⦌) a := by
    simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] using hv
  exact hv'

/-- A mono receiving lifts of all SAME original free simplices is the actual original whole isomorphism. -/
theorem isIso_of_simplexGenerator_lifts {C D : FixedObjects O} (f : C ⟶ D) [Mono f]
    (h : ∀ p : O × O × ℕ,
      Function.Surjective (fun k : simplexGenerator O p ⟶ C => k ≫ f)) : IsIso f := by
  apply isIso_of_homMap f
  intro x y
  let _ : (evaluation x y).IsRightAdjoint := (FreeSingleHom.adjunction x y).isRightAdjoint
  let _ : Mono (homMap f x y) := inferInstanceAs (Mono ((evaluation x y).map f))
  have hfq (q : SimplexCategoryᵒᵖ) : IsIso ((homMap f x y).app q) := by
    rcases q with ⟨⟨n⟩⟩
    apply (isIso_iff_bijective _).mpr
    refine ⟨injective_of_mono _, ?_⟩
    intro a
    let k := FreeSingleHom.extend x y (Δ[n] : SSet.{u}) D (SSet.yonedaEquiv.symm a)
    obtain ⟨l, hl⟩ := h (x, y, n) k
    let z := SSet.yonedaEquiv (FreeSingleHom.restrict x y (Δ[n] : SSet.{u}) C l)
    refine ⟨z, ?_⟩
    have he := congrArg (FreeSingleHom.restrict x y (Δ[n] : SSet.{u}) D) hl
    change FreeSingleHom.restrict x y (Δ[n] : SSet.{u}) D (l ≫ f) =
      FreeSingleHom.restrict x y (Δ[n] : SSet.{u}) D k at he
    rw [FreeSingleHom.restrict_comp, FreeSingleHom.restrict_extend] at he
    have hv := congrArg SSet.yonedaEquiv he
    simpa only [z, SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] using hv
  let _ : ∀ q, IsIso ((homMap f x y).app q) := hfq
  exact NatIso.isIso_of_isIso_app _

/-- The SAME actual free standard-simplex family is genuinely a strong generator. -/
theorem simplexGenerators_strong : (simplexGenerators O).IsStrongGenerator := by
  apply ObjectProperty.isStrongGenerator_iff.mpr
  refine ⟨simplexGenerators_separating, ?_⟩
  intro C D f hf h
  exact isIso_of_simplexGenerator_lifts f (fun p => h _ ⟨p⟩)

variable (O)

/-- The original fixed-label category is genuinely locally finitely presentable, with all original Homs retained. -/
instance locallyFinitelyPresentable : IsLocallyFinitelyPresentable.{u} (FixedObjects O) := by
  let _ : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    (FixedObjects O) Cardinal.aleph0).mpr
  refine ⟨simplexGenerators O, inferInstance, simplexGenerators_strong, ?_⟩
  rintro C ⟨p⟩
  exact inferInstanceAs (IsFinitelyPresentable.{u} (simplexGenerator O p))

/-- The SAME original fixed-label category is locally presentable at every larger regular rank. -/
theorem locallyPresentable_of_aleph0_le (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) : IsCardinalLocallyPresentable (FixedObjects O) κ := by
  let _ : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  exact IsCardinalLocallyPresentable.of_le (FixedObjects O) hκ

end CategoryTheory.SimplicialEnrichment.FixedObjects
