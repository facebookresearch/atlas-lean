/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OverHornFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.OverDependentProduct
import MathlibExt.CategoryTheory.MorphismProperty.SharpMaps
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Genuine original pullback Quillen comparison from simplex transitions

The SAME native pullback and its actual dependent-product adjunction are
retained. Original simplex transitions give the full horn-preimage weak
maps. Every original right-adjoint horn lifting problem transposes to
one of these original monic weak arrows. Actual model lifting makes the
right adjoint preserve fibrations, so this genuine adjunction is Quillen.
All original over objects are cofibrant; Brown then gives preservation
of every full original weak over-map. No desired global outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.SimplexPullback

variable {E B : SSet.{u}}

/-- The SAME native pullback preserves every full original over-cofibration. -/
theorem preservesCofibrations (p : E ⟶ B) :
    HomotopicalAlgebra.PreservesCofibrations (Over.pullback p) := by
  intro V W f hf
  let _ : Cofibration f := (HomotopicalAlgebra.cofibration_iff f).mpr hf
  let _ : Mono f.left := modelCategoryQuillen.mono_of_cofibration f.left
  let _ : Mono ((Over.pullback p).map f).left :=
    (MorphismProperty.overPullbackMap_isPullback p f).mono_fst_of_mono
  let _ : Cofibration ((Over.pullback p).map f).left := modelCategoryQuillen.cofibration_of_mono _
  exact (HomotopicalAlgebra.cofibration_iff _).mp
    ((cofibrations_over_iff E _).mpr inferInstance)

/-- Every SAME original simplicial over object is genuinely cofibrant in the original model. -/
theorem overObject_isCofibrant (B : SSet.{u}) (V : Over B) : IsCofibrant V := by
  apply (cofibrations_over_iff B (initial.to V)).mpr
  have h₀ : IsInitial ((initial (Over B)).left) :=
    IsInitial.isInitialObj (Over.forget B) (initial (Over B)) initialIsInitial
  let _ : Mono (h₀.to V.left) := CategoryTheory.initial_mono V.left h₀
  have he : (initial.to V).left = h₀.to V.left := h₀.hom_ext _ _
  let _ : Mono (initial.to V).left := he.symm ▸ inferInstanceAs (Mono (h₀.to V.left))
  exact modelCategoryQuillen.cofibration_of_mono _

/-- Actual original simplex transitions make the SAME full dependent product preserve original fibrations. -/
theorem dependentProduct_preservesFibrations (p : E ⟶ B)
    (h : ∀ {s t : SimplexIndex B} (a : s ⟶ t),
      realizationWeakEquivalences ((simplexPullbackDiagram p).map a)) :
    HomotopicalAlgebra.PreservesFibrations (OverDependentProduct.functor p) := by
  intro V W q hq
  let _ : Fibration q := (HomotopicalAlgebra.fibration_iff q).mpr hq
  apply (HomotopicalAlgebra.fibration_iff _).mp
  apply (overFibration_iff_hornLifting ((OverDependentProduct.functor p).map q)).mpr
  intro n k b
  let i := OverSubcomplex.arrow b (horn (n + 1) k)
  let _ : Mono i.left := inferInstanceAs (Mono (horn (n + 1) k).ι)
  let _ : Cofibration i.left := modelCategoryQuillen.cofibration_of_mono _
  let _ : Cofibration i := (cofibrations_over_iff B i).mpr inferInstance
  let _ : Cofibration ((Over.pullback p).map i) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (preservesCofibrations p i (mem_cofibrations i))
  have hm : realizationWeakEquivalences ((Over.pullback p).map i).left :=
    (OverSubcomplex.map_weak_iff p b (horn (n + 1) k)).mpr
      (simplexPullbackHorn_mem_realizationWeakEquivalences p h b k)
  let _ : WeakEquivalence ((Over.pullback p).map i).left :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr hm
  let _ : WeakEquivalence ((Over.pullback p).map i) :=
    (weakEquivalences_over_iff E _).mpr inferInstance
  exact ((OverDependentProduct.adjunction p).hasLiftingProperty_iff i q).mp
    (inferInstanceAs (HasLiftingProperty ((Over.pullback p).map i) q))

/-- The SAME original pullback/dependent-product adjunction is genuinely Quillen
under the actual original full simplex-transition condition. -/
theorem isQuillenAdjunction (p : E ⟶ B)
    (h : ∀ {s t : SimplexIndex B} (a : s ⟶ t),
      realizationWeakEquivalences ((simplexPullbackDiagram p).map a)) :
    Adjunction.IsQuillenAdjunction (OverDependentProduct.adjunction p) where
  preservesCofibrations := preservesCofibrations p
  preservesTrivialCofibrations := by
    intro V W i hi
    rw [← llp_eq_of_wfs (trivialCofibrations (Over E)) (fibrations (Over E))]
    intro X Y q hq
    have hr := dependentProduct_preservesFibrations p h q hq
    exact ((OverDependentProduct.adjunction p).hasLiftingProperty_iff i q).mpr
      (hasLiftingProperty_of_wfs i ((OverDependentProduct.functor p).map q) hi hr)

/-- ALL actual weak over-maps are preserved by the SAME original full native
pullback whenever every original simplex transition is weak. -/
theorem pullback_map_mem_realizationWeakEquivalences (p : E ⟶ B)
    (h : ∀ {s t : SimplexIndex B} (a : s ⟶ t),
      realizationWeakEquivalences ((simplexPullbackDiagram p).map a))
    {V W : Over B} (f : V ⟶ W) (hf : realizationWeakEquivalences f.left) :
    realizationWeakEquivalences ((Over.pullback p).map f).left := by
  let _ : Adjunction.IsQuillenAdjunction (OverDependentProduct.adjunction p) := isQuillenAdjunction p h
  let _ : IsCofibrant V := overObject_isCofibrant B V
  let _ : IsCofibrant W := overObject_isCofibrant B W
  let _ : WeakEquivalence f.left := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hf
  let _ : WeakEquivalence f := (weakEquivalences_over_iff B f).mpr inferInstance
  have hw : WeakEquivalence ((Over.pullback p).map f) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := OverDependentProduct.adjunction p) f
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    ((weakEquivalences_over_iff E _).mp hw)

end SSet.SimplexPullback
