/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected.lean` and
`P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected.lean`,
and
`Theorems/Thm_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective.lean` and
`P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometrically connected morphisms

Results on geometrically connected morphisms of schemes.

## Main results

- `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected`: a
  geometrically irreducible morphism is geometrically connected. An
  irreducible space is connected, universally: the implication lifts to
  morphism properties via the universal quantifier over base change.
- `AlgebraicGeometry.GeometricallyConnected.connectedSpace_pullback`: an
  instance saying that for a geometrically connected `f : X ⟶ Y`, a field `K`
  and `k : Spec K ⟶ Y`, the geometric fiber `X ×[Y] Spec K` is a connected
  space.
- `AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective`: if
  `f ≫ g` is geometrically connected and `f` is surjective, then `g` is
  geometrically connected, since each geometric fiber of `g` is a continuous
  surjective image of the corresponding fiber of `f ≫ g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- A geometrically irreducible morphism is geometrically connected. -/
theorem AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] :
    GeometricallyConnected f := by
  refine ⟨?_⟩
  have h := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f)
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono ?_ _ h
  intro X' Y' g hg hI hS
  have : IrreducibleSpace X' := hg hI hS
  infer_instance

/-- Every geometric fiber of a geometrically connected morphism is connected:
for a geometrically connected `f : X ⟶ Y`, a field `K` and `k : Spec K ⟶ Y`,
the pullback `X ×[Y] Spec K` is a connected space. As an instance, it lets
typeclass search supply the connectedness of these fibers. -/
instance AlgebraicGeometry.GeometricallyConnected.connectedSpace_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyConnected f]
    (K : Type u) [Field K] (k : Spec (.of K) ⟶ Y) :
    ConnectedSpace ↥(Limits.pullback f k) :=
  pullback_of_geometrically
    GeometricallyConnected.geometrically_connectedSpace K k

/-- Geometric connectedness of a composite `f ≫ g` descends to `g` when
`f` is surjective: every geometric fiber of `g` is a continuous surjective
image of the corresponding fiber of the composite. -/
theorem AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩
  let φ : Limits.pullback (f ≫ g) k ⟶ Limits.pullback g k :=
    Limits.pullback.map (f ≫ g) k g k f (𝟙 _) (𝟙 Z)
      (Category.comp_id _) (by simp)
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun {X Y Z} f g hf hg => letI := hf; letI := hg; inferInstance⟩
  have hφ : Surjective φ :=
    MorphismProperty.pullbackMap (P := @Surjective.{u}) ‹Surjective f›
      inferInstance rfl (Category.id_comp _).symm
  rw [connectedSpace_iff_univ, ← hφ.surj.range_eq]
  exact isConnected_range φ.continuous
