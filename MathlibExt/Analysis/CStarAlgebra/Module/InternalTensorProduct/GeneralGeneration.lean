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
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Bounds
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Creation
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Countable generation of internal tensor products

Let `E₁` be a complete right module over nonunital `D` and `E₂` a complete right module over
nonunital `B`. A complex nonunital star representation `φ : D → End_B(E₂)` defines a completed
internal tensor presentation `X` with pure map `p(x,y)` and dense pure span.

If both factors are countably generated in their right-coefficient norms, then `X` is countably
generated over `B`. Pairs of component generators `p(x_m,y_n)` generate it. No
countable-generation assumption on `D` or `B`, or nondegeneracy assumption on `φ`, is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule.InternalTensorProduct.IsModel

universe uD uB uE1 uE2 uX

variable {D : Type uD} [NonUnitalCStarAlgebra D]
  [PartialOrder Dᵐᵒᵖ]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E1 : Type uE1} [NormedAddCommGroup E1] [NormedSpace ℂ E1]
  [SMul Dᵐᵒᵖ E1] [CStarModule Dᵐᵒᵖ E1] [CompleteSpace E1]
variable {E2 : Type uE2} [NormedAddCommGroup E2] [NormedSpace ℂ E2]
  [SMul Bᵐᵒᵖ E2] [CStarModule Bᵐᵒᵖ E2] [CompleteSpace E2]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X] [CompleteSpace X]
variable {φ : D →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B E2}
variable {pure : E1 → E2 → X}

/-- **Countable generation of an internal tensor.** Let `D,B` be nonunital C-star algebras, with a
partial order on `Dᵐᵒᵖ` and star-compatible order on `Bᵐᵒᵖ`. Let `E₁,E₂` be complete right
modules over `D,B`, and `φ : D → End_B(E₂)` a complex nonunital star homomorphism. For a
complete right `B`-module `X` and pure map `p` satisfying `IsModel φ p`, countable generation
of both factors implies countable generation of `X` over `B` by pairs of their generators. -/
theorem countablyGenerated
    (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (h1 : CStarModule.IsCountablyGenerated (B := D) (E := E1))
    (h2 : CStarModule.IsCountablyGenerated (B := B) (E := E2)) :
    CStarModule.IsCountablyGenerated (B := B) (E := X) := by
  classical
  rcases h1 with ⟨s1, hs1⟩
  rcases h2 with ⟨s2, hs2⟩
  let z : ℕ → X := fun n => pure (s1 (Nat.unpair n).1) (s2 (Nat.unpair n).2)
  let T : Submodule ℂ X := Submodule.span ℂ
    (Set.range fun p : ℕ × B => z p.1 <• p.2)
  let S : Submodule ℂ X := T.topologicalClosure
  have hSclosed : IsClosed (S : Set X) := T.isClosed_topologicalClosure
  let D1 : Submodule ℂ E1 := Submodule.span ℂ
    (Set.range fun p : ℕ × D => s1 p.1 <• p.2)
  let D2 : Submodule ℂ E2 := Submodule.span ℂ
    (Set.range fun p : ℕ × B => s2 p.1 <• p.2)
  have hD1top : D1.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hs1
  have hD2top : D2.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hs2
  have hgenerator (n m : ℕ) (b : B) :
      pure (s1 n) (s2 m <• b) ∈ S := by
    rw [hX.2.2.2.2.2.1]
    have hpair : pure (s1 n) (s2 m) = z (Nat.pair n m) := by
      simp only [z, Nat.unpair_pair]
    rw [hpair]
    exact T.le_topologicalClosure (Submodule.subset_span ⟨(Nat.pair n m, b), rfl⟩)
  have hfixed (n : ℕ) (y : E2) : pure (s1 n) y ∈ S := by
    let L : E2 →L[ℂ] X :=
      (CStarModule.InternalTensorProduct.creationOnModel φ pure hX (s1 n)).toContinuousLinearMap
    let U : Submodule ℂ E2 := S.comap L.toLinearMap
    have hUclosed : IsClosed (U : Set E2) := by
      change IsClosed (L ⁻¹' (S : Set X))
      exact hSclosed.preimage L.continuous
    have hD2U : D2 ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨m, b⟩, rfl⟩
      apply Submodule.mem_comap.mpr
      change CStarModule.InternalTensorProduct.creationOnModel φ pure hX (s1 n)
        (s2 m <• b) ∈ S
      rw [CStarModule.InternalTensorProduct.creationOnModel_apply]
      exact hgenerator n m b
    have hUtop : (⊤ : Submodule ℂ E2) ≤ U := by
      rw [← hD2top]
      exact D2.topologicalClosure_minimal hD2U hUclosed
    have hy : L y ∈ S := Submodule.mem_comap.mp (hUtop (by trivial))
    change CStarModule.InternalTensorProduct.creationOnModel φ pure hX (s1 n) y ∈ S at hy
    simpa only [CStarModule.InternalTensorProduct.creationOnModel_apply] using hy
  have hpure (x : E1) (y : E2) : pure x y ∈ S := by
    let L : E1 →L[ℂ] X := hX.pureLeftCLM y
    let U : Submodule ℂ E1 := S.comap L.toLinearMap
    have hUclosed : IsClosed (U : Set E1) := by
      change IsClosed (L ⁻¹' (S : Set X))
      exact hSclosed.preimage L.continuous
    have hD1U : D1 ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨n, d⟩, rfl⟩
      apply Submodule.mem_comap.mpr
      change hX.pureLeftCLM y (s1 n <• d) ∈ S
      rw [pureLeftCLM_apply, hX.2.2.2.2.1]
      exact hfixed n (φ d y)
    have hUtop : (⊤ : Submodule ℂ E1) ≤ U := by
      rw [← hD1top]
      exact D1.topologicalClosure_minimal hD1U hUclosed
    have hx : L x ∈ S := Submodule.mem_comap.mp (hUtop (by trivial))
    simpa only [L, pureLeftCLM_apply] using hx
  let P : Submodule ℂ X := Submodule.span ℂ
    (Set.range fun p : E1 × E2 => pure p.1 p.2)
  have hPS : P ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hpure x y
  have hPtop : P.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hX.2.2.2.2.2.2.2
  have hStop : S = ⊤ := by
    apply le_antisymm le_top
    rw [← hPtop]
    exact P.topologicalClosure_minimal hPS hSclosed
  exact ⟨z, Submodule.dense_iff_topologicalClosure_eq_top.mpr hStop⟩

end CStarModule.InternalTensorProduct.IsModel
