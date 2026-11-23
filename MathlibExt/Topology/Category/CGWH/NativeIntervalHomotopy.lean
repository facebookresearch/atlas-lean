/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CompactParameterEvaluation
public import MathlibExt.Topology.Category.CGWH.RealizedInterval
public import Mathlib.Topology.Homotopy.Basic
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# The actual native interval map as an ordinary whole homotopy

The original native interval is compact Hausdorff through its original
clock homeomorphism. Existing compact-parameter evaluation therefore
converts a native whole homotopy to an ordinary jointly continuous map,
with no local-compactness condition on the active source. Both original
endpoint equations are retained.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u v

namespace CGWH

attribute [local instance] CGWH.cartesianBraidedCategory

private local instance actualIntervalCompact : CompactSpace nativeInterval.{u, v} :=
  ⟨by
    have h := (isCompact_univ : IsCompact (Set.univ : Set unitInterval)).image
      (nativeIntervalHomeomorph.{u, v}.symm.continuous)
    have hr : Set.range nativeIntervalHomeomorph.{u, v}.symm = Set.univ :=
      nativeIntervalHomeomorph.{u, v}.symm.surjective.range_eq
    simpa only [Set.image_univ, hr] using h⟩

private local instance actualIntervalT2 : T2Space nativeInterval.{u, v} :=
  nativeIntervalHomeomorph.{u, v}.symm.t2Space

private local instance actualIntervalLocallyCompact : LocallyCompactSpace nativeInterval.{u, v} :=
  inferInstance

variable {A M : CGWH.{u, v}}

private def nativeIntervalMapRecipe (H : nativeInterval.{u, v} ⊗ A ⟶ M) :
    C(unitInterval × A, M) :=
  let p := (β_ A nativeInterval.{u, v}).hom ≫ H
  let f := MonoidalClosed.curry p
  (compactParameterEvaluationMap f).comp
    ((nativeIntervalHomeomorph.{u, v}.symm : C(unitInterval, nativeInterval.{u, v})).prodMap
      (ContinuousMap.id A))

private theorem nativeIntervalMapRecipe_apply
    (H : nativeInterval.{u, v} ⊗ A ⟶ M) (t : unitInterval) (a : A) :
    nativeIntervalMapRecipe H (t, a) = H (tensorMk (nativeIntervalHomeomorph.{u, v}.symm t) a) := by
  let p := (β_ A nativeInterval.{u, v}).hom ≫ H
  let f := MonoidalClosed.curry p
  have hc := internalHom_curry_apply p (tensorMk a (nativeIntervalHomeomorph.{u, v}.symm t))
  rw [tensorMk_fst, tensorMk_snd] at hc
  change compactParameterEvaluationMap f (nativeIntervalHomeomorph.{u, v}.symm t, a) = _
  exact (compactParameterEvaluationMap_apply f (nativeIntervalHomeomorph.{u, v}.symm t) a).trans
    (hc.trans (by rw [ConcreteCategory.comp_apply, tensorMk_braiding]))

/-- The whole ordinary interval map of the SAME native interval homotopy. -/
public def ordinaryNativeIntervalMap (H : nativeInterval.{u, v} ⊗ A ⟶ M) :
    C(unitInterval × A, M) := nativeIntervalMapRecipe H

/-- Every interval and active-source value is the SAME native paired value. -/
public theorem ordinaryNativeIntervalMap_apply
    (H : nativeInterval.{u, v} ⊗ A ⟶ M) (t : unitInterval) (a : A) :
    ordinaryNativeIntervalMap H (t, a) = H (tensorMk (nativeIntervalHomeomorph.{u, v}.symm t) a) := by
  unfold ordinaryNativeIntervalMap
  exact nativeIntervalMapRecipe_apply H t a

private theorem nativeEndpoint_zero_value (H : nativeInterval.{u, v} ⊗ A ⟶ M) (a : A) :
    ((λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 0 ▷ A) ≫ H) a =
      H (tensorMk (nativeIntervalHomeomorph.{u, v}.symm 0) a) := by
  rw [ConcreteCategory.comp_apply, leftUnitor_inv_tensorMk,
    ConcreteCategory.comp_apply, tensorMk_whiskerRight, nativeIntervalEndpoint_zero_apply.{u, v}]

private theorem nativeEndpoint_one_value (H : nativeInterval.{u, v} ⊗ A ⟶ M) (a : A) :
    ((λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 1 ▷ A) ≫ H) a =
      H (tensorMk (nativeIntervalHomeomorph.{u, v}.symm 1) a) := by
  rw [ConcreteCategory.comp_apply, leftUnitor_inv_tensorMk,
    ConcreteCategory.comp_apply, tensorMk_whiskerRight, nativeIntervalEndpoint_one_apply.{u, v}]

/-- A whole native interval map with the two ORIGINAL endpoint equations
constructs an actual ordinary homotopy on the ENTIRE original active space. -/
public def ordinaryHomotopyOfNativeInterval
    (f g : A ⟶ M) (H : nativeInterval.{u, v} ⊗ A ⟶ M)
    (h₀ : (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 0 ▷ A) ≫ H = f)
    (h₁ : (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 1 ▷ A) ≫ H = g) :
    ContinuousMap.Homotopy (ConcreteCategory.hom (C := CGWH.{u, v}) f)
      (ConcreteCategory.hom (C := CGWH.{u, v}) g) where
  toContinuousMap := ordinaryNativeIntervalMap H
  map_zero_left a := (ordinaryNativeIntervalMap_apply H 0 a).trans
    ((nativeEndpoint_zero_value H a).symm.trans (ConcreteCategory.congr_hom h₀ a))
  map_one_left a := (ordinaryNativeIntervalMap_apply H 1 a).trans
    ((nativeEndpoint_one_value H a).symm.trans (ConcreteCategory.congr_hom h₁ a))

/-- Every value of the ordinary homotopy is the original native value, on the full clock. -/
public theorem ordinaryHomotopyOfNativeInterval_apply
    (f g : A ⟶ M) (H : nativeInterval.{u, v} ⊗ A ⟶ M)
    (h₀ : (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 0 ▷ A) ≫ H = f)
    (h₁ : (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 1 ▷ A) ≫ H = g)
    (t : unitInterval) (a : A) :
    ordinaryHomotopyOfNativeInterval f g H h₀ h₁ (t, a) =
      H (tensorMk (nativeIntervalHomeomorph.{u, v}.symm t) a) :=
  ordinaryNativeIntervalMap_apply H t a

/-- A proved WHOLE native interval map fixes its actual selected point
through the ordinary conversion, with both ORIGINAL endpoint maps. -/
public def ordinaryPointRelativeHomotopyOfNativeInterval
    (f g : A ⟶ M) (H : nativeInterval.{u, v} ⊗ A ⟶ M)
    (h₀ : (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 0 ▷ A) ≫ H = f)
    (h₁ : (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} 1 ▷ A) ≫ H = g)
    (a : A) (hpoint : ∀ s, H (tensorMk s a) = f a) :
    ContinuousMap.HomotopyRel (ConcreteCategory.hom (C := CGWH.{u, v}) f)
      (ConcreteCategory.hom (C := CGWH.{u, v}) g) {a} where
  toHomotopy := ordinaryHomotopyOfNativeInterval f g H h₀ h₁
  prop' t b hb := by
    have hba : b = a := Set.mem_singleton_iff.mp hb
    subst b
    unfold ordinaryHomotopyOfNativeInterval
    exact (ordinaryNativeIntervalMap_apply H t a).trans
      (hpoint (nativeIntervalHomeomorph.{u, v}.symm t))

end CGWH

end
