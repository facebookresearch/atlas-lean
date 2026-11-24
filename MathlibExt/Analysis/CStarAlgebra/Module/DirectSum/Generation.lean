/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.Generation
public import Mathlib.Logic.Encodable.Basic

/-!
# Countable generation of completed Hilbert-module direct sums

A countable direct sum of countably generated complete right modules is
countably generated.  The proof enumerates component generators and uses the
dense span of the literal completed coordinate inclusions.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped RightActions

namespace CStarModule.DirectSum

universe uB uI uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {I : Type uI} {E : I → Type uE}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]
variable [∀ i, CompleteSpace (E i)]

/-- A countable completed direct sum of countably generated components is
countably generated. -/
theorem isCountablyGenerated_completed
    [Countable I]
    (hE : ∀ i, CStarModule.IsCountablyGenerated (B := B) (E := E i)) :
    CStarModule.IsCountablyGenerated (B := B) (E := Completed B E) := by
  let gE : ∀ i, ℕ → E i := fun i ↦ Classical.choose (hE i)
  have hgE (i : I) :
      Dense (Submodule.span ℂ
        (Set.range fun p : ℕ × B ↦ gE i p.1 <• p.2) : Set (E i)) :=
    Classical.choose_spec (hE i)
  let _ : Encodable I := Encodable.ofCountable I
  let g : ℕ → Completed B E := fun n =>
    match (Encodable.decode n : Option (Σ i, ℕ)) with
    | some p => completedSingle (B := B) (E := E) p.1 (gE p.1 p.2)
    | none => 0
  let M : Submodule ℂ (Completed B E) :=
    Submodule.span ℂ (Set.range fun p : ℕ × B ↦ g p.1 <• p.2)
  let C : Submodule ℂ (Completed B E) := M.topologicalClosure
  have hCclosed : IsClosed (C : Set (Completed B E)) :=
    M.isClosed_topologicalClosure
  have hsingle (i : I) (x : E i) :
      completedSingle (B := B) (E := E) i x ∈ C := by
    let L := (completedSingle (B := B) (E := E) i).toContinuousLinearMap
    let U : Submodule ℂ (E i) := Submodule.comap L.toLinearMap C
    have hUclosed : IsClosed (U : Set (E i)) := by
      change IsClosed (L ⁻¹' (C : Set (Completed B E)))
      exact hCclosed.preimage L.continuous
    have hspan :
        Submodule.span ℂ (Set.range fun p : ℕ × B ↦ gE i p.1 <• p.2) ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨n, b⟩, rfl⟩
      apply Submodule.mem_comap.mpr
      change completedSingle (B := B) (E := E) i (gE i n <• b) ∈ C
      rw [completedSingle_right_smul]
      let k := Encodable.encode (⟨i, n⟩ : Σ i, ℕ)
      have hg : g k =
          completedSingle (B := B) (E := E) i (gE i n) := by
        simp [k, g, Encodable.encodek]
      rw [← hg]
      exact M.le_topologicalClosure
        (Submodule.subset_span ⟨(k, b), by
          simp [k, g, Encodable.encodek]⟩)
    have hUtop : (⊤ : Submodule ℂ (E i)) ≤ U := by
      rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp (hgE i)]
      exact Submodule.topologicalClosure_minimal _ hspan hUclosed
    exact Submodule.mem_comap.mp (hUtop (by trivial))
  refine ⟨g, Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_⟩
  apply top_unique
  intro x _
  let P : Submodule ℂ (Completed B E) :=
    Submodule.span ℂ
      (Set.range fun p : Σ i, E i ↦ completedSingle (B := B) (E := E) p.1 p.2)
  have hPC : P ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact hsingle p.1 p.2
  have hPtop : P.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp
      (dense_span_completedSingle (B := B) (E := E))
  have hCtop : C = ⊤ := by
    apply le_antisymm le_top
    rw [← hPtop]
    exact Submodule.topologicalClosure_minimal _ hPC hCclosed
  change x ∈ C
  rw [hCtop]
  trivial

end CStarModule.DirectSum
