/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.RelativeProjectivity

/-!
# Normalized birational resolutions

Birationality is Mathlib's `Scheme.BirationalOver`: an actual dense-open
isomorphism whose map is the restriction of the given scheme morphism.
A resolution has a smooth integral source, a locally projective proper morphism,
and an isomorphism over every smooth open of the original variety.

Local projectivity uses actual closed immersions into projective space
on affine opens of the target. This records local projectivity without
identifying it with a global embedding into `P^N_X`.

References: Hironaka, *Resolution of singularities of an algebraic variety
over a field of characteristic zero*, Ann. Math. 79 (1964), Parts I–II;
Stacks Project, Tag 0BHW (definition of a resolution).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BirationalResolution

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeProjectivity

universe u

/-- The condition that `f : Y ⟶ X` is birational: there are dense open subschemes `U ⊆ Y` and
`V ⊆ X` and an isomorphism `U ≅ V` whose composite with the inclusion of `V` is the restriction of
`f` to `U`. That is, `Y` is birational to `X` over `X` via `f` and `𝟙 X`
(`Scheme.BirationalOver f (𝟙 X)`). -/
abbrev IsBirationalMorphism {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  Scheme.BirationalOver f (𝟙 X)

theorem isBirationalMorphism_id (X : Scheme.{u}) :
    IsBirationalMorphism (𝟙 X) :=
  Scheme.BirationalOver.refl (𝟙 X)

/-- Restriction of the actual morphism and its field structure to a target open. -/
def restrictOver {k : Type u} [Field k]
    {Y X : Over (Spec (.of k))} (f : Y ⟶ X) (U : X.left.Opens) :
    Over.mk ((f.left ⁻¹ᵁ U).ι ≫ Y.hom) ⟶ Over.mk (U.ι ≫ X.hom) :=
  Over.homMk (f.left.resLE U (f.left ⁻¹ᵁ U) le_rfl) (by
    change (f.left.resLE U (f.left ⁻¹ᵁ U) le_rfl) ≫ (U.ι ≫ X.hom) =
      (f.left ⁻¹ᵁ U).ι ≫ Y.hom
    rw [← Category.assoc,
      Scheme.Hom.resLE_comp_ι,
      Category.assoc, f.w])

/-- Local projectivity: over each point of the target, the restriction to an affine open
neighbourhood is H-projective (over an affine base, H-projective and projective agree,
Stacks, Tag 01WB). -/
def IsLocallyProjectiveOver {k : Type u} [Field k]
    {Y X : Over (Spec (.of k))} (f : Y ⟶ X) : Prop :=
  ∀ x : X.left, ∃ U : X.left.affineOpens, x ∈ U.1 ∧
    IsHProjectiveOver (restrictOver f U.1)

/-- A resolution with its genuine geometric morphism and local normalization. -/
structure ResolutionModel {k : Type u} [Field k]
    (X : Over (Spec (.of k))) where
  source : Over (Spec (.of k))
  [integral : IsIntegral source.left]
  [smooth : Smooth source.hom]
  morphism : source ⟶ X
  [proper : IsProper morphism.left]
  locallyProjective : IsLocallyProjectiveOver morphism
  birational : IsBirationalMorphism morphism.left
  unchangedSmooth : ∀ U : X.left.Opens,
    Smooth (U.ι ≫ X.hom) →
      IsIso (morphism.left.resLE U (morphism.left ⁻¹ᵁ U) le_rfl)

end MathlibExt.AlgebraicGeometry.BirationalResolution
