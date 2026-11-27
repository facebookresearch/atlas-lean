/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Naturality squares for homology maps

Homology sends a commuting square of short complexes or homological
complexes to a commuting square.  The raw equality form is convenient for
rewriting; the `CommSq` form supports categorical square composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {S₀ S₁ S₂ S₃ : ShortComplex C}
  [S₀.HasHomology] [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology]
variable {f : S₀ ⟶ S₁} {g : S₀ ⟶ S₂}
  {h : S₁ ⟶ S₃} {i : S₂ ⟶ S₃}

/-- Homology maps preserve a commuting square of short complexes. -/
@[reassoc]
theorem homologyMap_square (sq : f ≫ h = g ≫ i) :
    homologyMap f ≫ homologyMap h = homologyMap g ≫ homologyMap i := by
  rw [← homologyMap_comp, sq, homologyMap_comp]

/-- Bundled homology square associated to a commuting square of short
complexes. -/
theorem homologyMap_commSq (sq : CommSq f g h i) :
    CommSq (homologyMap f) (homologyMap g)
      (homologyMap h) (homologyMap i) :=
  ⟨homologyMap_square sq.w⟩

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {ι : Type w} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {c : ComplexShape ι}
variable {K₀ K₁ K₂ K₃ : HomologicalComplex C c}
variable {f : K₀ ⟶ K₁} {g : K₀ ⟶ K₂}
  {h : K₁ ⟶ K₃} {i : K₂ ⟶ K₃}

/-- Homology maps preserve a commuting square of homological complexes. -/
@[reassoc]
theorem homologyMap_square (sq : f ≫ h = g ≫ i) (n : ι)
    [K₀.HasHomology n] [K₁.HasHomology n]
    [K₂.HasHomology n] [K₃.HasHomology n] :
    homologyMap f n ≫ homologyMap h n =
      homologyMap g n ≫ homologyMap i n := by
  rw [← homologyMap_comp, ← homologyMap_comp, sq]

/-- Bundled homology square associated to a commuting square of homological
complexes. -/
theorem homologyMap_commSq (sq : CommSq f g h i) (n : ι)
    [K₀.HasHomology n] [K₁.HasHomology n]
    [K₂.HasHomology n] [K₃.HasHomology n] :
    CommSq (homologyMap f n) (homologyMap g n)
      (homologyMap h n) (homologyMap i n) :=
  ⟨homologyMap_square sq.w n⟩

end HomologicalComplex
