/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Generation
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Bounds
import MathlibExt.Analysis.CStarAlgebra.Module.Factorization
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Countable generation of coefficient base-change models

The same internal-tensor model supplies its pure map, Gram formula and dense
span. Both opposite-order dictionaries are retained. The shared arbitrary-order
factorization corollary derives Gram positivity, without replacing the caller order.
The target coefficient self-module need not be countably generated.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped CStarModule.Right RightActions

namespace CStarModule.InternalTensorProduct.IsModel

universe uB₁ uB₂ uE uX

variable {B₁ : Type uB₁} {B₂ : Type uB₂} {E : Type uE} {X : Type uX}
variable [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul B₁ᵐᵒᵖ E]
  [CStarModule B₁ᵐᵒᵖ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul B₂ᵐᵒᵖ X]
  [CStarModule B₂ᵐᵒᵖ X] [CompleteSpace X]
variable {g : B₁ →⋆ₙₐ[ℂ] B₂} {pure : E → B₂ → X}

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E and X be complete normed right inner-product modules over B₁ and
B₂, respectively, with compatible complex normed-space structures. Let g : B₁ → B₂ be a
nonunital complex star homomorphism, and suppose pure : E × B₂ → X satisfies the internal-tensor
laws for the left multiplication representation induced by g and has dense complex-linear span.

If E is countably generated over B₁, then X is countably generated over B₂.
-/
theorem countablyGenerated_baseChange
    (hX : CStarModule.InternalTensorProduct.IsModel
      ((CStarModule.AdjointableOperator.leftRegular (B := B₂)).comp g) pure)
    (hE : CStarModule.IsCountablyGenerated (B := B₁) (E := E)) :
    CStarModule.IsCountablyGenerated (B := B₂) (E := X) := by
  classical
  rcases hE with ⟨s, hs⟩
  let D : Submodule ℂ E := Submodule.span ℂ
    (Set.range fun p : ℕ × B₁ => s p.1 <• p.2)
  have hDtop : D.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hs
  have hfactor (n : ℕ) : ∃ y : E, ∃ c : B₁, s n = y <• c := by
    exact CStarModule.exists_right_factor_of_starOrderedRing (B := B₁) (E := E) (s n)
  let y : ℕ → E := fun n => Classical.choose (hfactor n)
  let c : ℕ → B₁ := fun n => Classical.choose (Classical.choose_spec (hfactor n))
  have hy (n : ℕ) : s n = y n <• c n :=
    Classical.choose_spec (Classical.choose_spec (hfactor n))
  let z : ℕ → X := fun n => pure (y n) (g (c n))
  let T : Submodule ℂ X := Submodule.span ℂ
    (Set.range fun p : ℕ × B₂ => z p.1 <• p.2)
  let S : Submodule ℂ X := T.topologicalClosure
  have hSclosed : IsClosed (S : Set X) := T.isClosed_topologicalClosure
  have hbalance (x : E) (b : B₁) (d : B₂) :
      pure (x <• b) d = pure x (g b * d) := by
    simpa only [NonUnitalStarAlgHom.comp_apply,
      CStarModule.AdjointableOperator.leftRegular_apply] using
        hX.2.2.2.2.1 x b d
  have hgen (n : ℕ) (b : B₁) (d : B₂) :
      pure (s n <• b) d = z n <• (g b * d) := by
    calc
      pure (s n <• b) d = pure ((y n <• c n) <• b) d := by rw [hy n]
      _ = pure (y n <• (c n * b)) d := by rw [CStarModule.right_smul_mul]
      _ = pure (y n) (g (c n * b) * d) := hbalance (y n) (c n * b) d
      _ = pure (y n) (g (c n) * (g b * d)) := by rw [map_mul, mul_assoc]
      _ = pure (y n) (g (c n) <• (g b * d)) := by
        rw [CStarModule.Right.right_smul_self]
      _ = pure (y n) (g (c n)) <• (g b * d) :=
        hX.2.2.2.2.2.1 (y n) (g (c n)) (g b * d)
      _ = z n <• (g b * d) := rfl
  have hpure (x : E) (d : B₂) : pure x d ∈ S := by
    let L : E →L[ℂ] X := hX.pureLeftCLM d
    let U : Submodule ℂ E := Submodule.comap L.toLinearMap S
    have hUclosed : IsClosed (U : Set E) := by
      change IsClosed (L ⁻¹' (S : Set X))
      exact hSclosed.preimage L.continuous
    have hDU : D ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨n, b⟩, rfl⟩
      apply Submodule.mem_comap.mpr
      change L (s n <• b) ∈ S
      rw [show L (s n <• b) = pure (s n <• b) d from
        CStarModule.InternalTensorProduct.IsModel.pureLeftCLM_apply hX _ d]
      rw [hgen n b d]
      exact T.le_topologicalClosure
        (Submodule.subset_span ⟨(n, g b * d), rfl⟩)
    have hUtop : (⊤ : Submodule ℂ E) ≤ U := by
      rw [← hDtop]
      exact D.topologicalClosure_minimal hDU hUclosed
    have hxU : x ∈ U := hUtop (by trivial)
    have hxL : L x ∈ S := Submodule.mem_comap.mp hxU
    simpa only [L, CStarModule.InternalTensorProduct.IsModel.pureLeftCLM_apply] using hxL
  let P : Submodule ℂ X := Submodule.span ℂ
    (Set.range fun p : E × B₂ => pure p.1 p.2)
  have hPS : P ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, d⟩, rfl⟩
    exact hpure x d
  have hPtop : P.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hX.2.2.2.2.2.2.2
  have hStop : S = ⊤ := by
    apply le_antisymm le_top
    rw [← hPtop]
    exact P.topologicalClosure_minimal hPS hSclosed
  exact ⟨z, Submodule.dense_iff_topologicalClosure_eq_top.mpr hStop⟩

end CStarModule.InternalTensorProduct.IsModel
