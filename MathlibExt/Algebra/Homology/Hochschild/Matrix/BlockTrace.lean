/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.GeneralizedTrace
public import Mathlib.Data.Matrix.Block

/-!
# Generalized trace of a lower matrix block

Let k be commutative, A,M k-modules and J a finite index type.
Place the coefficient matrix and every tail matrix in the lower J×J
block of matrices indexed by PUnit⊕J, with all other blocks zero.
Their generalized tensor trace equals the generalized trace over J.

Each closed cycle entering the added PUnit block contributes zero.
The surviving ordered cycles have indices in J. This includes J empty.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w z

namespace ModuleCat.Algebra.Hochschild.Matrix

variable (k : Type u) [CommRing k]
  {A : Type v} [AddCommGroup A] [Module k A]
  {M : Type w} [AddCommGroup M] [Module k M]
  (J : Type z) [Fintype J]

/-- Let k be commutative, A,M k-modules and J finite. For a
coefficient X and tail B_j indexed by J,
Tr_{PUnit⊕J}(diag(0,X)⊗diag(0,B_1)⊗⋯⊗diag(0,B_n))
=Tr_J(X⊗B_1⊗⋯⊗B_n). All off-lower-block entries are zero. -/
theorem generalizedTrace_fromBlocks (n : ℕ) (X : Matrix J J M)
    (a : Fin n → Matrix J J A) :
    generalizedTrace k (PUnit ⊕ J) n
        ((Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 X) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun i =>
            Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (a i))) =
      generalizedTrace k J n (X ⊗ₜ[k] PiTensorProduct.tprod k a) := by
  classical
  rw [generalizedTrace_tmul_tprod, generalizedTrace_tmul_tprod]
  let e : (Fin (n + 1) → J) → (Fin (n + 1) → PUnit ⊕ J) := fun γ i => Sum.inr (γ i)
  have he : Function.Injective e := by
    intro γ δ h
    funext i
    exact Sum.inr_injective (congrFun h i)
  let f : (Fin (n + 1) → J) → M ⊗[k] TensorPower k n A := fun γ =>
    X (γ 0) (γ 1) ⊗ₜ[k]
      PiTensorProduct.tprod k (fun j => a j (γ j.succ) (γ (j.succ + 1)))
  let g : (Fin (n + 1) → PUnit ⊕ J) → M ⊗[k] TensorPower k n A := fun γ =>
    (Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 X) (γ 0) (γ 1) ⊗ₜ[k]
      PiTensorProduct.tprod k (fun j =>
        (Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (a j))
          (γ j.succ) (γ (j.succ + 1)))
  have hz (γ : Fin (n + 1) → PUnit ⊕ J) (hγ : γ ∉ Set.range e) : g γ = 0 := by
    have hex : ∃ i : Fin (n + 1), ∃ p : PUnit, γ i = Sum.inl p := by
      by_contra hn
      have hright (i : Fin (n + 1)) : ∃ j : J, γ i = Sum.inr j := by
        cases hi : γ i with
        | inl p => exact False.elim (hn ⟨i, p, hi⟩)
        | inr j => exact ⟨j, rfl⟩
      choose δ hδ using hright
      apply hγ
      refine ⟨δ, ?_⟩
      funext i
      exact (hδ i).symm
    obtain ⟨i, p, hp⟩ := hex
    cases i using Fin.cases with
    | zero =>
      cases h1 : γ 1 with
      | inl q =>
        simp only [g, hp, h1, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply,
          TensorProduct.zero_tmul]
      | inr q =>
        simp only [g, hp, h1, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
          TensorProduct.zero_tmul]
    | succ j =>
      have ha : (Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (a j))
          (γ j.succ) (γ (j.succ + 1)) = 0 := by
        cases hj : γ (j.succ + 1) with
        | inl q => simp only [hp, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
        | inr q => simp only [hp, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      have ht := (PiTensorProduct.tprod k).map_coord_zero
        (m := fun l =>
          (Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (a l))
            (γ l.succ) (γ (l.succ + 1))) j ha
      change (Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 X) (γ 0) (γ 1) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j =>
          (Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (a j))
            (γ j.succ) (γ (j.succ + 1))) = 0
      rw [ht, TensorProduct.tmul_zero]
  have hv (γ : Fin (n + 1) → J) : f γ = g (e γ) := by
    simp only [f, g, e, Matrix.fromBlocks_apply₂₂]
  exact (Fintype.sum_of_injective e he f g hz hv).symm

end ModuleCat.Algebra.Hochschild.Matrix
