/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology maps determined by a single degree component

Let C be a category with zero morphisms. For short complexes S and T
whose homology exists, two maps S → T induce the same homology map
whenever their middle components S₂ → T₂ agree.

For a complex shape c on an arbitrary index type ι, chain maps K → L
therefore have equal maps on H_i whenever their degree-i components
agree, provided H_i(K) and H_i(L) exist. A zero degree-i component
induces the zero homology map, and an identity degree-i component of
an endomorphism induces id on H_i. The object, morphism and index
universes are independent; no abelian or preadditive structure is
required beyond the stated existence of homology.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S T : ShortComplex C} [S.HasHomology] [T.HasHomology]

/-- Let C be a category with zero morphisms, and let S,T be
short complexes in C with homology. If two maps f,g : S → T have
the same middle component S₂ → T₂, then H(f) = H(g).
The left and right components may differ. -/
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

/-- For a category C with zero morphisms, an arbitrary complex
shape c on ι and complexes K,L whose homology exists at i ∈ ι,
maps f,g : K → L induce H_i(f) = H_i(g) whenever their degree-i
components K_i → L_i agree. -/
theorem homologyMap_eq_of_component (f g : K ⟶ L) (h : f.f i = g.f i) :
    homologyMap f i = homologyMap g i :=
  CategoryTheory.ShortComplex.homologyMap_eq_of_middle
    ((shortComplexFunctor C c i).map f) ((shortComplexFunctor C c i).map g) h

/-- For complexes K,L of any shape in a category with zero
morphisms, with homology at i, a chain map f : K → L whose
degree-i component is zero satisfies H_i(f) = 0. -/
theorem homologyMap_eq_zero_of_component (f : K ⟶ L) (h : f.f i = 0) : homologyMap f i = 0 := by
  rw [homologyMap_eq_of_component i f 0 h, homologyMap_zero]

/-- For a complex K of any shape in a category with zero
morphisms, with homology at i, an endomorphism f whose degree-i
component is id_(K_i) satisfies H_i(f) = id_(H_i(K)). -/
theorem homologyMap_eq_id_of_component (f : K ⟶ K) (h : f.f i = 𝟙 (K.X i)) :
    homologyMap f i = 𝟙 (K.homology i) := by
  rw [homologyMap_eq_of_component i f (𝟙 K) h, homologyMap_id]

end HomologicalComplex
