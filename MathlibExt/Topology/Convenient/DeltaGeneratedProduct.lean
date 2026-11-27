/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import MathlibExt.Topology.Convenient.QuotientProduct

/-!
# Product of Delta-generated spaces with locally compact left factor.

The ordinary product of two Delta-generated spaces is Delta-generated when
the left factor is locally compact, via the staged evaluation-quotient route.
-/

@[expose] public section

open Topology

namespace DeltaGeneratedSpace

private abbrev EvalIdx (Y : Type*) [TopologicalSpace Y] : Type _ :=
  (n : ℕ) × ContinuousMap ((fun n ↦ Fin n → ℝ) n) Y

private abbrev EvalDom (Y : Type*) [TopologicalSpace Y] : Type _ :=
  (f : EvalIdx Y) × (fun n ↦ Fin n → ℝ) f.1

private def evalMap (Y : Type*) [TopologicalSpace Y] : EvalDom Y → Y :=
  fun x => x.1.2 x.2

private lemma isQuotientMap_eval (Y : Type*) [TopologicalSpace Y]
    [DeltaGeneratedSpace Y] : IsQuotientMap (evalMap Y) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    have hEq1 : (‹TopologicalSpace Y›) =
        TopologicalSpace.generatedBy (fun n ↦ Fin n → ℝ) :=
      (IsGeneratedBy.generatedBy_eq).symm
    have hEq2 : TopologicalSpace.generatedBy (fun n ↦ Fin n → ℝ) (Y := Y) =
        TopologicalSpace.coinduced (evalMap Y) inferInstance :=
      TopologicalSpace.generatedBy_eq_coinduced (X := fun n ↦ Fin n → ℝ) (Y := Y)
    exact hEq1.trans hEq2
  · intro y
    refine ⟨⟨⟨0, ContinuousMap.const _ y⟩, fun _ => 0⟩, ?_⟩
    simp only [evalMap, ContinuousMap.const_apply]

/-- Finite Euclidean products are `DeltaGeneratedSpace`.

This is only the generator-pair case needed for the `HomSpace` curry API.
No arbitrary product, exponential, subspace, realization, or model-category claim. -/
instance prod_finPi_isGeneratedBy (m n : ℕ) :
    IsGeneratedBy (fun n : ℕ => Fin n → ℝ) ((Fin m → ℝ) × (Fin n → ℝ)) :=
  (Fin.appendHomeomorph m n).symm.isQuotientMap.isGeneratedBy

/-- The ordinary product of two Delta-generated spaces is Delta-generated when the left factor
is locally compact. No claim is made for arbitrary products of Delta-generated spaces. -/
theorem prod_of_locallyCompact_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [DeltaGeneratedSpace X] [DeltaGeneratedSpace Y] :
    DeltaGeneratedSpace (X × Y) := by
  have hQX : IsQuotientMap (evalMap X) := isQuotientMap_eval X
  have hQY : IsQuotientMap (evalMap Y) := isQuotientMap_eval Y
  have hXE : ∀ n, IsGeneratedBy (fun n ↦ Fin n → ℝ) (X × (Fin n → ℝ)) := by
    intro n
    have hSrc : IsGeneratedBy (fun n ↦ Fin n → ℝ) (EvalDom X × (Fin n → ℝ)) := by
      have hFib : ∀ p : EvalIdx X, IsGeneratedBy (fun n ↦ Fin n → ℝ)
          (((fun n ↦ Fin n → ℝ) p.1) × (Fin n → ℝ)) := by
        intro p
        exact inferInstance
      have hSigma : IsGeneratedBy (fun n ↦ Fin n → ℝ)
          (Σ p : EvalIdx X, (((fun n ↦ Fin n → ℝ) p.1) × (Fin n → ℝ))) := by
        have := hFib
        exact inferInstance
      have hDist : (EvalDom X × (Fin n → ℝ)) ≃ₜ
          (Σ p : EvalIdx X, (((fun n ↦ Fin n → ℝ) p.1) × (Fin n → ℝ))) :=
        Homeomorph.sigmaProdDistrib
      have := hSigma
      exact hDist.symm.isQuotientMap.isGeneratedBy
    have := hSrc
    have hQf : IsQuotientMap
      (Prod.map (evalMap X) id : EvalDom X × (Fin n → ℝ) → X × (Fin n → ℝ)) :=
      hQX.prodMap_left
    exact hQf.isGeneratedBy
  have hEX : ∀ m, IsGeneratedBy (fun n ↦ Fin n → ℝ) ((Fin m → ℝ) × X) := by
    intro m
    have := hXE m
    exact (Homeomorph.prodComm X (Fin m → ℝ)).isQuotientMap.isGeneratedBy
  have hDYX : IsGeneratedBy (fun n ↦ Fin n → ℝ) (EvalDom Y × X) := by
    have hFib2 : ∀ q : EvalIdx Y, IsGeneratedBy (fun n ↦ Fin n → ℝ)
        (((fun n ↦ Fin n → ℝ) q.1) × X) := by
      intro q
      exact hEX q.1
    have hSigma2 : IsGeneratedBy (fun n ↦ Fin n → ℝ)
        (Σ q : EvalIdx Y, (((fun n ↦ Fin n → ℝ) q.1) × X)) := by
      have := hFib2
      exact inferInstance
    have hDist2 : (EvalDom Y × X) ≃ₜ
        (Σ q : EvalIdx Y, (((fun n ↦ Fin n → ℝ) q.1) × X)) :=
      Homeomorph.sigmaProdDistrib
    have := hSigma2
    exact hDist2.symm.isQuotientMap.isGeneratedBy
  have hXDY : IsGeneratedBy (fun n ↦ Fin n → ℝ) (X × EvalDom Y) := by
    have := hDYX
    exact (Homeomorph.prodComm _ _).isQuotientMap.isGeneratedBy
  have := hXDY
  have hQfinal : IsQuotientMap (Prod.map id (evalMap Y) : X × EvalDom Y → X × Y) :=
    hQY.prodMap_right
  exact hQfinal.isGeneratedBy

end DeltaGeneratedSpace
