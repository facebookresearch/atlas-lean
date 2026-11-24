/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy
public import MathlibExt.Topology.Convenient.QuotientProduct

/-!
# Products of compactly generated spaces with a locally compact factor

A product of two `u`-compactly generated spaces is again `u`-compactly
generated when either factor is locally compact Hausdorff.  The proof uses
two evaluation quotient maps and keeps the compact-probe and carrier
universes independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open Topology

private abbrev EvalIdx (Y : Type v) [TopologicalSpace Y] : Type _ :=
  (K : CompHaus.{u}) × C(K, Y)

private abbrev EvalDom (Y : Type v) [TopologicalSpace Y] : Type _ :=
  (p : EvalIdx.{u, v} Y) × p.1

private def evalMap (Y : Type v) [TopologicalSpace Y] :
    EvalDom.{u, v} Y → Y :=
  fun z ↦ z.1.2 z.2

private lemma evalMap_isQuotientMap
    (Y : Type v) [TopologicalSpace Y]
    [UCompactlyGeneratedSpace.{u} Y] :
    IsQuotientMap (evalMap.{u, v} Y) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  have hGenerated : IsGeneratedBy P Y :=
    (isGeneratedBy_compactHausProbes_iff (Y := Y)).2 inferInstance
  let _ : IsGeneratedBy P Y := hGenerated
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    have hEq₁ : (inferInstance : TopologicalSpace Y) =
        TopologicalSpace.generatedBy P :=
      IsGeneratedBy.generatedBy_eq.symm
    have hEq₂ : TopologicalSpace.generatedBy P (Y := Y) =
        TopologicalSpace.coinduced (evalMap.{u, v} Y) inferInstance :=
      by
        change TopologicalSpace.generatedBy P =
          TopologicalSpace.coinduced
            (fun z : (p : EvalIdx.{u, v} Y) × p.1 => z.1.2 z.2)
              inferInstance
        exact TopologicalSpace.generatedBy_eq_coinduced (X := P) (Y := Y)
    exact hEq₁.trans hEq₂
  · intro y
    let K : CompHaus.{u} := CompHaus.of (ULift.{u} (Fin 1))
    refine ⟨⟨⟨K, ContinuousMap.const K y⟩, ULift.up (0 : Fin 1)⟩, ?_⟩
    rfl

private theorem isGeneratedBy_prod_compHaus
    {A : Type w} [TopologicalSpace A]
    [UCompactlyGeneratedSpace.{u} A]
    (S : CompHaus.{u}) :
    IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} (A × S) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  have hFiber : ∀ p : EvalIdx.{u, w} A,
      IsGeneratedBy P (p.1 × S) := by
    intro p
    change IsGeneratedBy P (P (CompHaus.of (p.1 × S)))
    infer_instance
  have hSigma : IsGeneratedBy P
      (Σ p : EvalIdx.{u, w} A, p.1 × S) := by
    let _ : ∀ p : EvalIdx.{u, w} A,
        IsGeneratedBy P (p.1 × S) := hFiber
    infer_instance
  let hDist : EvalDom.{u, w} A × S ≃ₜ
      (Σ p : EvalIdx.{u, w} A, p.1 × S) :=
    Homeomorph.sigmaProdDistrib
  have hEvalDom : IsGeneratedBy P (EvalDom.{u, w} A × S) := by
    let _ : IsGeneratedBy P
        (Σ p : EvalIdx.{u, w} A, p.1 × S) := hSigma
    exact hDist.symm.isQuotientMap.isGeneratedBy
  have hQ : IsQuotientMap
      (Prod.map (evalMap.{u, w} A) (id : S → S) :
        EvalDom.{u, w} A × S → A × S) :=
    (evalMap_isQuotientMap.{u, w} A).prodMap_left
  let _ : IsGeneratedBy P (EvalDom.{u, w} A × S) := hEvalDom
  exact hQ.isGeneratedBy

/-- A product of `u`-compactly generated spaces is `u`-compactly generated
when the left factor is locally compact Hausdorff. -/
theorem uCompactlyGeneratedSpace_prod_of_locallyCompact_left
    {A : Type w} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyCompactSpace A] [T2Space A]
    [UCompactlyGeneratedSpace.{u} A]
    [UCompactlyGeneratedSpace.{u} B] :
    UCompactlyGeneratedSpace.{u} (A × B) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  have hAS (S : CompHaus.{u}) : IsGeneratedBy P (A × S) :=
    isGeneratedBy_prod_compHaus.{u, w} S
  have hFiber : ∀ q : EvalIdx.{u, v} B,
      IsGeneratedBy P (q.1 × A) := by
    intro q
    let _ : IsGeneratedBy P (A × q.1) := hAS q.1
    exact (Homeomorph.prodComm A q.1).isQuotientMap.isGeneratedBy
  have hSigma : IsGeneratedBy P
      (Σ q : EvalIdx.{u, v} B, q.1 × A) := by
    let _ : ∀ q : EvalIdx.{u, v} B,
        IsGeneratedBy P (q.1 × A) := hFiber
    infer_instance
  let hDist : EvalDom.{u, v} B × A ≃ₜ
      (Σ q : EvalIdx.{u, v} B, q.1 × A) :=
    Homeomorph.sigmaProdDistrib
  have hEvalDomRight : IsGeneratedBy P (EvalDom.{u, v} B × A) := by
    let _ : IsGeneratedBy P
        (Σ q : EvalIdx.{u, v} B, q.1 × A) := hSigma
    exact hDist.symm.isQuotientMap.isGeneratedBy
  have hAEvalDom : IsGeneratedBy P (A × EvalDom.{u, v} B) := by
    let _ : IsGeneratedBy P (EvalDom.{u, v} B × A) := hEvalDomRight
    exact (Homeomorph.prodComm (EvalDom.{u, v} B) A).isQuotientMap.isGeneratedBy
  have hQ : IsQuotientMap
      (Prod.map id (evalMap.{u, v} B) :
        A × EvalDom.{u, v} B → A × B) :=
    (evalMap_isQuotientMap.{u, v} B).prodMap_right
  let _ : IsGeneratedBy P (A × EvalDom.{u, v} B) := hAEvalDom
  exact isGeneratedBy_compactHausProbes_iff.1 hQ.isGeneratedBy

/-- A product of `u`-compactly generated spaces is `u`-compactly generated
when the right factor is locally compact Hausdorff. -/
theorem uCompactlyGeneratedSpace_prod_of_locallyCompact_right
    {A : Type w} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyCompactSpace B] [T2Space B]
    [UCompactlyGeneratedSpace.{u} A]
    [UCompactlyGeneratedSpace.{u} B] :
    UCompactlyGeneratedSpace.{u} (A × B) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  have hBA : UCompactlyGeneratedSpace.{u} (B × A) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
      (A := B) (B := A)
  have hGeneratedBA : IsGeneratedBy P (B × A) :=
    isGeneratedBy_compactHausProbes_iff.2 hBA
  let _ : IsGeneratedBy P (B × A) := hGeneratedBA
  have hGeneratedAB : IsGeneratedBy P (A × B) :=
    (Homeomorph.prodComm B A).isQuotientMap.isGeneratedBy
  exact isGeneratedBy_compactHausProbes_iff.1 hGeneratedAB
