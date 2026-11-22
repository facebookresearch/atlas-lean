/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_
of_range_eq.lean`,
`P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq.lean`,
`Theorems/Thm_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale.lean`,
`P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale.lean`,
`Theorems/Thm_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_
of_isPullback_of_surjective.lean` and
`P2M/Sol/S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_
of_isPullback_of_surjective.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Closed and open immersions

Two reduced closed immersions with the same range are isomorphic; a closed
immersion whose composite with an étale map is flat and locally of finite
presentation is open; and closed immersions, surjectivity, separatedness,
universal closedness, and properness transfer along pullback squares with a
surjective closed immersion on the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Two reduced closed immersions with the same range are isomorphic over
the target. -/
theorem AlgebraicGeometry.IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq
    {A B X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) [IsClosedImmersion f]
    [IsClosedImmersion g] [IsReduced A] [IsReduced B]
    (h : Set.range f.base = Set.range g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by
  have : Surjective (pullback.fst f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, ← h, Set.preimage_range]⟩
  have : Surjective (pullback.snd f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, h, Set.preimage_range]⟩
  have : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso (pullback.snd f g) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨(asIso (pullback.fst f g)).symm ≪≫ asIso (pullback.snd f g), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
  rw [IsIso.inv_comp_eq, pullback.condition]

/-- A closed immersion whose composite with an étale map is flat and
locally of finite presentation is open. -/
theorem AlgebraicGeometry.IsOpenImmersion.of_isClosedImmersion_of_flat_comp_of_etale
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsClosedImmersion i] [Etale g]
    [Flat (i ≫ g)] [LocallyOfFinitePresentation (i ≫ g)] :
    IsOpenImmersion i ∧ Etale (i ≫ g) := by
  have hmono : Mono i := inferInstance
  have hdiag : IsOpenImmersion (Limits.pullback.diagonal i) := inferInstance
  have hi : FormallyUnramified i := inferInstance
  have hg : FormallyUnramified g := inferInstance
  have hig : FormallyUnramified (i ≫ g) := MorphismProperty.comp_mem _ i g hi hg
  have het : Etale (i ≫ g) := Etale.of_formallyUnramified_of_flat (f := i ≫ g)
  have heti : Etale i := Etale.of_comp i g
  have hflat : Flat i := (Etale.iff_flat_and_formallyUnramified.mp heti).1
  have hlfp : LocallyOfFinitePresentation i :=
    (Etale.iff_flat_and_formallyUnramified.mp heti).2.2
  exact ⟨IsOpenImmersion.of_flat_of_mono i, het⟩

/-- Closed immersions transfer along pullback squares. -/
theorem AlgebraicGeometry.IsClosedImmersion.of_isPullback
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hg.flip inferInstance

/-- Surjectivity transfers along pullback squares. -/
theorem AlgebraicGeometry.Surjective.of_isPullback
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    Surjective g :=
  MorphismProperty.of_isPullback (P := @Surjective) hg.flip inferInstance

/-- Universal closedness transfers along a pullback square whose base map is
a surjective closed immersion. -/
theorem AlgebraicGeometry.UniversallyClosed.of_isPullback
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i)
    [UniversallyClosed f₀] : UniversallyClosed f := by
  have : Surjective g := Surjective.of_isPullback i hg
  have : UniversallyClosed (g ≫ f) := by rw [hg.w]; infer_instance
  exact UniversallyClosed.of_comp_surjective g f

/-- Separatedness transfers along a pullback square whose base map is a
surjective closed immersion. -/
theorem AlgebraicGeometry.IsSeparated.of_isPullback
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i)
    [IsSeparated f₀] : IsSeparated f := by
  have : Surjective g := Surjective.of_isPullback i hg
  have : IsClosedImmersion g := IsClosedImmersion.of_isPullback i hg
  have e₁ : f₀ ≫ i = g ≫ f := hg.w.symm
  let k : pullback (f₀ ≫ i) (f₀ ≫ i) ⟶ pullback f f :=
    pullback.map (f₀ ≫ i) (f₀ ≫ i) f f g g (𝟙 S) ((Category.comp_id _).trans e₁)
      ((Category.comp_id _).trans e₁)
  have : MorphismProperty.IsStableUnderComposition (P := @IsClosedImmersion) :=
    ⟨fun _ _ _ _ => inferInstance⟩
  have hk : IsClosedImmersion k :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹IsClosedImmersion g›
      ‹IsClosedImmersion g› e₁ e₁
  have hΔ₀ : IsClosedImmersion (pullback.diagonal (f₀ ≫ i)) := inferInstance
  have hcomp : g ≫ pullback.diagonal f = pullback.diagonal (f₀ ≫ i) ≫ k := by
    apply pullback.hom_ext
    · simp only [k, Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc,
        pullback.diagonal_fst]
      rfl
    · simp only [k, Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc,
        pullback.diagonal_snd]
      rfl
  have hclosedcomp : IsClosedImmersion (pullback.diagonal (f₀ ≫ i) ≫ k) := inferInstance
  have hrange : Set.range (pullback.diagonal f).base =
      Set.range (pullback.diagonal (f₀ ≫ i) ≫ k).base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨y₀, rfl⟩ := g.surjective y
      refine ⟨y₀, ?_⟩
      change (pullback.diagonal (f₀ ≫ i) ≫ k) y₀ = (g ≫ pullback.diagonal f) y₀
      rw [hcomp]
    · rintro ⟨y₀, rfl⟩
      refine ⟨g.base y₀, ?_⟩
      change (g ≫ pullback.diagonal f) y₀ = (pullback.diagonal (f₀ ≫ i) ≫ k) y₀
      rw [hcomp]
  have hclosed : IsClosed (Set.range (pullback.diagonal f).base) := by
    rw [hrange]
    exact hclosedcomp.isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

/-- Properness transfers along a pullback square whose base map is a
surjective closed immersion. -/
theorem AlgebraicGeometry.IsProper.of_isPullback
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i)
    [IsProper f₀] [LocallyOfFiniteType f] : IsProper f := by
  have := IsSeparated.of_isPullback i hg
  have := UniversallyClosed.of_isPullback i hg
  exact (isProper_iff f).mpr ⟨‹_›, ‹_›, ‹_›⟩
