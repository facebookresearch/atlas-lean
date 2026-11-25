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

public import MathlibExt.Analysis.CStarAlgebra.Module.Generation
public import MathlibExt.Analysis.CStarAlgebra.Module.Product.Basic
public import Mathlib.Logic.Equiv.Nat

/-!
# Countable generation of binary C-star-module products

Two generating sequences are interleaved.  Density is transported through
the actual adjointable coordinate inclusions, so the theorem uses the
coefficient-inner-product product topology.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped RightActions

namespace CStarModule.IsCountablyGenerated

universe uB uE uF

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. If E and F are complete
countably generated right Hilbert B-modules, their two-factor Hilbert-module product is
countably generated. -/
theorem prod
    (hE : CStarModule.IsCountablyGenerated (B := B) (E := E))
    (hF : CStarModule.IsCountablyGenerated (B := B) (E := F)) :
    CStarModule.IsCountablyGenerated
      (B := B) (E := CStarModule.Product B E F) := by
  rcases hE with ⟨gE, hgE⟩
  rcases hF with ⟨gF, hgF⟩
  let g : ℕ → CStarModule.Product B E F := fun n =>
    match Equiv.natSumNatEquivNat.symm n with
    | Sum.inl k => CStarModule.Product.inl (B := B) (E := E) (F := F) (gE k)
    | Sum.inr k => CStarModule.Product.inr (B := B) (E := E) (F := F) (gF k)
  let M : Submodule ℂ (CStarModule.Product B E F) :=
    Submodule.span ℂ (Set.range fun p : ℕ × B ↦ g p.1 <• p.2)
  let C : Submodule ℂ (CStarModule.Product B E F) := M.topologicalClosure
  have hCclosed : IsClosed (C : Set (CStarModule.Product B E F)) :=
    M.isClosed_topologicalClosure
  have hinl (x : E) :
      CStarModule.Product.inl (B := B) (E := E) (F := F) x ∈ C := by
    let L := CStarModule.Product.inl (B := B) (E := E) (F := F)
    let U : Submodule ℂ E := Submodule.comap L.toContinuousLinearMap.toLinearMap C
    have hUclosed : IsClosed (U : Set E) := by
      change IsClosed (L ⁻¹' (C : Set (CStarModule.Product B E F)))
      exact hCclosed.preimage L.toContinuousLinearMap.continuous
    have hspan :
        Submodule.span ℂ (Set.range fun p : ℕ × B ↦ gE p.1 <• p.2) ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨n, b⟩, rfl⟩
      apply Submodule.mem_comap.mpr
      change L (gE n <• b) ∈ C
      rw [L.map_right_smul]
      have hg : g (Equiv.natSumNatEquivNat (Sum.inl n)) = L (gE n) := by
        simp [g, L]
        rfl
      rw [← hg]
      exact M.le_topologicalClosure
        (Submodule.subset_span ⟨(Equiv.natSumNatEquivNat (Sum.inl n), b), by simp [g]⟩)
    have hUtop : (⊤ : Submodule ℂ E) ≤ U := by
      rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp hgE]
      exact Submodule.topologicalClosure_minimal _ hspan hUclosed
    exact Submodule.mem_comap.mp (hUtop (by trivial))
  have hinr (x : F) :
      CStarModule.Product.inr (B := B) (E := E) (F := F) x ∈ C := by
    let L := CStarModule.Product.inr (B := B) (E := E) (F := F)
    let U : Submodule ℂ F := Submodule.comap L.toContinuousLinearMap.toLinearMap C
    have hUclosed : IsClosed (U : Set F) := by
      change IsClosed (L ⁻¹' (C : Set (CStarModule.Product B E F)))
      exact hCclosed.preimage L.toContinuousLinearMap.continuous
    have hspan :
        Submodule.span ℂ (Set.range fun p : ℕ × B ↦ gF p.1 <• p.2) ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨n, b⟩, rfl⟩
      apply Submodule.mem_comap.mpr
      change L (gF n <• b) ∈ C
      rw [L.map_right_smul]
      have hg : g (Equiv.natSumNatEquivNat (Sum.inr n)) = L (gF n) := by
        simp [g, L]
        rfl
      rw [← hg]
      exact M.le_topologicalClosure
        (Submodule.subset_span ⟨(Equiv.natSumNatEquivNat (Sum.inr n), b), by simp [g]⟩)
    have hUtop : (⊤ : Submodule ℂ F) ≤ U := by
      rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp hgF]
      exact Submodule.topologicalClosure_minimal _ hspan hUclosed
    exact Submodule.mem_comap.mp (hUtop (by trivial))
  refine ⟨g, Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_⟩
  apply top_unique
  intro x _
  have hsum := C.add_mem (hinl x.1) (hinr x.2)
  have hdecomp :
      CStarModule.Product.inl (B := B) (E := E) (F := F) x.1 +
        CStarModule.Product.inr (B := B) (E := E) (F := F) x.2 = x := by
    apply (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).injective
    apply Prod.ext
    · change x.1 + 0 = x.1
      simp
    · change 0 + x.2 = x.2
      simp
  rwa [hdecomp] at hsum

end CStarModule.IsCountablyGenerated
