/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Formally unramified restrictions of a composite

The restriction of a composite `f ≫ g` over an open `U` of the target is formally unramified
when the restrictions of `g` over `U` and of `f` over `g⁻¹ U` are. This is the inclusion
`Crit(g ∘ f) ⊆ Crit(g) ∪ g(Crit(f))` for the critical values of a composite of morphisms of
curves, in the proof of Theorem 3.3 in B. Köck, *Belyi's theorem revisited*, Beitr. Algebra
Geom. 45 (2004), no. 1, 253–265, p. 262.

It combines Mathlib's `AlgebraicGeometry.morphismRestrict_comp` with the stability of
`AlgebraicGeometry.FormallyUnramified` under composition.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/-- **Branch locus of a composite.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and
`U` an open subscheme of `Z`. If the restriction `g⁻¹ U ⟶ U` of `g` is formally unramified and
the restriction `(f ≫ g)⁻¹ U ⟶ g⁻¹ U` of `f` is formally unramified, then the restriction
`(f ≫ g)⁻¹ U ⟶ U` of `f ≫ g` is formally unramified.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof of
Theorem 3.3, p. 262: "for any composition g ∘ f of morphisms between curves, we obviously have
Crit(g ∘ f) = Crit(g) ∪ g(Crit(f))". This is the inclusion `⊆` of that equality, in terms of
the open set over which a morphism is unramified. -/
theorem FormallyUnramified.morphismRestrict_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) [FormallyUnramified (g ∣_ U)] [FormallyUnramified (f ∣_ g ⁻¹ᵁ U)] :
    FormallyUnramified ((f ≫ g) ∣_ U) := by
  rw [AlgebraicGeometry.morphismRestrict_comp]
  exact MorphismProperty.comp_mem _ _ _ ‹_› ‹_›

end AlgebraicGeometry
