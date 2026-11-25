/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Actual homology maps depend on the original middle component

The native homology projection is epi and the native homology inclusion is
mono. The original native formula between them contains only the middle
component of a short-complex map. Cancelling those actual maps proves
componentwise equality, zero and identity laws for the original homology
map. These laws let locally finite chain projectors give genuinely finite
homology projector sums without a global coproduct exactness assumption.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S T : ShortComplex C} [S.HasHomology] [T.HasHomology]

/-- Cancelling the native homology epi and mono shows that equal original middle maps give equal homology maps. -/
theorem homologyMap_eq_of_middle (f g : S ⟶ T) (h : f.τ₂ = g.τ₂) :
    homologyMap f = homologyMap g := by
  apply (cancel_epi S.homologyπ).mp
  apply (cancel_mono T.homologyι).mp
  simpa only [Category.assoc, π_homologyMap_ι, h]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (i : ι) [K.HasHomology i] [L.HasHomology i]

/-- The actual original homology map depends only on the original chain-map component in that degree. -/
theorem homologyMap_eq_of_component (f g : K ⟶ L) (h : f.f i = g.f i) :
    homologyMap f i = homologyMap g i :=
  CategoryTheory.ShortComplex.homologyMap_eq_of_middle
    ((shortComplexFunctor C c i).map f) ((shortComplexFunctor C c i).map g) h

/-- A zero original middle component gives the actual zero homology map. -/
theorem homologyMap_eq_zero_of_component (f : K ⟶ L) (h : f.f i = 0) : homologyMap f i = 0 := by
  rw [homologyMap_eq_of_component i f 0 h, homologyMap_zero]

/-- An original identity component gives the actual identity endomorphism on the selected homology. -/
theorem homologyMap_eq_id_of_component (f : K ⟶ K) (h : f.f i = 𝟙 (K.X i)) :
    homologyMap f i = 𝟙 (K.homology i) := by
  rw [homologyMap_eq_of_component i f (𝟙 K) h, homologyMap_id]

end HomologicalComplex
