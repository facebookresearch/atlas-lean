/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalReplacement

/-! # Full generic clients of the original generated locality calculus -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory HomotopicalAlgebra
open HomotopicalAlgebra.GeneratedLocalReplacement

namespace GeneratedLocalReplacementClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The genuine original local Whitehead test remains available without a simplicial coefficient premise. -/
theorem source_only_whitehead {K : Type wS} (S : K → Arrow C) {X Y : C} (f : X ⟶ Y)
    (hX : generatedLocalFibrant d S X) (hY : generatedLocalFibrant d S Y) :
    generatedLocalEquivalences d S f ↔ weakEquivalences C f :=
  generatedLocalEquivalences_weak_iff_of_local d S f hX hY

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)
  [MorphismProperty.HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

include a in
/-- Both weak legs preserve the complete original source and target squares at every input. -/
theorem original_comparison_span {X Y Z T : C} (f : X ⟶ Y) (g : Z ⟶ T) :
    SSet.realizationWeakEquivalences (fromOriginal d X Z) ∧
    SSet.realizationWeakEquivalences (fromGenerated d X Z) ∧
    (derivedMappingPrecomp f Z ≫ fromOriginal d X Z = fromOriginal d Y Z ≫
      GeneratedDerivedMapping.precomp d ((cofibrantReplacement (C := C)).map f)
        ((fibrantReplacement (C := C)).obj Z)) ∧
    (GeneratedDerivedMapping.precomp d f Z ≫ fromGenerated d X Z = fromGenerated d Y Z ≫
      GeneratedDerivedMapping.precomp d ((cofibrantReplacement (C := C)).map f)
        ((fibrantReplacement (C := C)).obj Z)) ∧
    (derivedMappingPostcomp X g ≫ fromOriginal d X T = fromOriginal d X Z ≫
      GeneratedDerivedMapping.postcomp d ((cofibrantReplacement (C := C)).obj X)
        ((fibrantReplacement (C := C)).map g)) ∧
    (GeneratedDerivedMapping.postcomp d X g ≫ fromGenerated d X T = fromGenerated d X Z ≫
      GeneratedDerivedMapping.postcomp d ((cofibrantReplacement (C := C)).obj X)
        ((fibrantReplacement (C := C)).map g)) :=
  ⟨fromOriginal_weak d a X Z, fromGenerated_weak d a X Z,
    fromOriginal_source d f Z, fromGenerated_source d f Z,
    fromOriginal_target d X g, fromGenerated_target d X g⟩

omit [MorphismProperty.HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- Original derived locality gives the actual right lifting test at each original cotensor boundary. -/
theorem source_locality_gives_original_cotensor_tests {K : Type wS} (S : K → Arrow C)
    (Z : C) (hZ : generatedLocalFibrant d S Z) (n : ℕ) :
    generatedLocalFibrant d S ((a.cotensor.obj (.op (SSet.boundary n : SSet.{v}))).obj Z) ∧
      (generators d a S).rlp ((a.cotensor.map (SSet.boundary n).ι.op).app Z) :=
  ⟨cotensorBoundary_isLocal d a S Z hZ n, cotensorBoundaryMap_generators_rlp d a S Z hZ n⟩

end GeneratedLocalReplacementClients
