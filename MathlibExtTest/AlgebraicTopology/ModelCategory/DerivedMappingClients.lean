/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.Basic

/-!
# Clients of chosen derived mapping objects

The replacement squares use arbitrary arrows in the original category.
The mapping square computes the two actions in the raw simplicial enrichment.
-/

open CategoryTheory HomotopicalAlgebra MorphismProperty

variable {C : Type*} [Category* C] [ModelCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

example {X Y : C} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (cofibrantReplacement.map f) ∧
      WeakEquivalence (fibrantReplacement.map f) := by
  constructor
  · have h : WeakEquivalence ((cofibrantReplacementCounit (C := C)).app X ≫ f) := inferInstance
    have square : cofibrantReplacement.map f ≫ (cofibrantReplacementCounit (C := C)).app Y =
        (cofibrantReplacementCounit (C := C)).app X ≫ f :=
      (cofibrantReplacementCounit (C := C)).naturality f
    rw [← square] at h
    exact weakEquivalence_of_postcomp (cofibrantReplacement.map f)
      ((cofibrantReplacementCounit (C := C)).app Y)
  · have h : WeakEquivalence (f ≫ (fibrantReplacementUnit (C := C)).app Y) := inferInstance
    have square : f ≫ (fibrantReplacementUnit (C := C)).app Y =
        (fibrantReplacementUnit (C := C)).app X ≫ fibrantReplacement.map f :=
      (fibrantReplacementUnit (C := C)).naturality f
    rw [square] at h
    exact weakEquivalence_of_precomp ((fibrantReplacementUnit (C := C)).app X)
      (fibrantReplacement.map f)

example (X : C) :
    IsCofibrant ((cofibrantReplacement (C := C)).obj X) ∧
    IsFibrant ((fibrantReplacement (C := C)).obj X) ∧
    trivialFibrations C ((cofibrantReplacementCounit (C := C)).app X) ∧
    trivialCofibrations C ((fibrantReplacementUnit (C := C)).app X) :=
  ⟨inferInstance, inferInstance, mem_trivialFibrations _, mem_trivialCofibrations _⟩

example [SimplicialCategory C] {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    derivedMappingPrecomp f Y ≫ derivedMappingPostcomp X g =
      eHomWhiskerLeft SSet (cofibrantReplacement.obj X') (fibrantReplacement.map g) ≫
        eHomWhiskerRight SSet (cofibrantReplacement.map f) (fibrantReplacement.obj Y') := by
  rw [derivedMappingPrecomp_postcomp, derivedMappingPostcomp_eq_whisker,
    derivedMappingPrecomp_eq_whisker]
  rfl
