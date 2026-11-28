/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ZeroDifferentialHomology

/-!
# Naturality of classes in zero-differential complexes

When all differentials vanish, each degree object maps canonically to its
homology and is canonically isomorphic to it. These class morphisms are
natural under maps between zero-differential complexes.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}

/--
Let K be a c-complex in a category C with zero morphisms. Assume homology exists at i and
every differential of K is zero. The canonical class morphism Kᵢ→Hᵢ(K) is the inverse of the
zero-differential homology isomorphism Hᵢ(K)≅Kᵢ.
-/
theorem zeroDifferentialClassMap_eq_inv (K : HomologicalComplex C c) (i : ι)
    [K.HasHomology i] (hK : ∀ j k, K.d j k = 0) :
    zeroDifferentialClassMap K i hK = (zeroDifferentialHomologyIso K i hK).inv := by
  apply (cancel_mono (zeroDifferentialHomologyIso K i hK).hom).1
  rw [zeroDifferentialClassMap_homologyIso, Iso.inv_hom_id]

/--
Let f:K→L be a map of c-complexes in a category C with zero morphisms, assume both have zero
differentials and homology at i. For their class morphisms κ_K:Kᵢ→Hᵢ(K), κ_L:Lᵢ→Hᵢ(L),
κ_K≫Hᵢ(f)=fᵢ≫κ_L.
-/
@[reassoc]
theorem zeroDifferentialClassMap_naturality {K L : HomologicalComplex C c}
    (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : ∀ j k, K.d j k = 0) (hL : ∀ j k, L.d j k = 0) :
    zeroDifferentialClassMap K i hK ≫ homologyMap f i =
      f.f i ≫ zeroDifferentialClassMap L i hL := by
  rw [zeroDifferentialClassMap_eq_inv, zeroDifferentialClassMap_eq_inv]
  apply (cancel_mono (zeroDifferentialHomologyIso L i hL).hom).1
  rw [Category.assoc, zeroDifferentialHomologyIso_naturality f i hK hL,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HomologicalComplex
