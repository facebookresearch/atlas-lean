/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import MathlibExt.Combinatorics.DiscreteHolderBrascampLieb

@[expose] public section

open MathlibExt.Combinatorics.DiscreteHolderBrascampLiebWanted

namespace MathlibExtTest.Combinatorics.DiscreteHolderBrascampLieb

/-- The statement of Theorem 3.2 of arXiv:1308.0068, as the theorem states it. -/
example {d m : ℕ} (dj : Fin m → ℕ) (φ : (j : Fin m) → (Fin d → ℤ) →+ (Fin (dj j) → ℤ))
    (s : Fin m → ℝ) (hs : ∀ j, s j ∈ Set.Icc (0 : ℝ) 1) :
    (∀ H : AddSubgroup (Fin d → ℤ),
        (Module.finrank ℤ H : ℝ) ≤ ∑ j, s j * (Module.finrank ℤ (H.map (φ j)) : ℝ)) ↔
      ∀ E : Finset (Fin d → ℤ), E.Nonempty →
        (E.card : ℝ) ≤ ∏ j, ((E.image (φ j)).card : ℝ) ^ s j :=
  rank_le_iff_card_le_prod dj φ s hs

/-- Two copies of the identity of `ℤ^d` with exponents `1/2` satisfy the rank condition, so the
theorem gives `|E| ≤ |E|^{1/2} |E|^{1/2}` for every nonempty finite `E ⊆ ℤ^d`. -/
example {d : ℕ} (E : Finset (Fin d → ℤ)) (hE : E.Nonempty) :
    (E.card : ℝ) ≤
      ∏ j : Fin 2, ((E.image ((fun _ => AddMonoidHom.id (Fin d → ℤ)) j)).card : ℝ) ^
        ((fun _ => (1 / 2 : ℝ)) j) := by
  refine (rank_le_iff_card_le_prod (fun _ => d) (fun _ => AddMonoidHom.id (Fin d → ℤ))
    (fun _ => 1 / 2) fun _ => ⟨by norm_num, by norm_num⟩).mp (fun H => ?_) E hE
  have hH : Module.finrank ℤ (H.map (AddMonoidHom.id (Fin d → ℤ))) = Module.finrank ℤ H := by
    rw [AddSubgroup.map_id]
  simp only [Fin.sum_univ_two, hH]
  linarith

/-- Necessity: the zero map `ℤ → ℤ⁰` with exponent `1` violates the rank condition on `H = ℤ`
(rank `1` against `1 · 0`), so by the theorem some nonempty finite `E ⊆ ℤ` has
`|E| > |0(E)|^1 = 1`. -/
example : ¬ ∀ E : Finset (Fin 1 → ℤ), E.Nonempty →
    (E.card : ℝ) ≤ ∏ j : Fin 1,
      ((E.image ((fun _ => (0 : (Fin 1 → ℤ) →+ (Fin 0 → ℤ))) j)).card : ℝ) ^
        ((fun _ => (1 : ℝ)) j) := by
  intro h
  have h1 := (rank_le_iff_card_le_prod (fun _ => 0) (fun _ => (0 : (Fin 1 → ℤ) →+ (Fin 0 → ℤ)))
    (fun _ => 1) fun _ => ⟨zero_le_one, le_rfl⟩).mpr h ⊤
  have htop : Module.finrank ℤ (⊤ : AddSubgroup (Fin 1 → ℤ)) = 1 := by
    rw [AddSubgroup.topEquiv.toIntLinearEquiv.finrank_eq, Module.finrank_pi, Fintype.card_fin]
  have hbot : Module.finrank ℤ ((⊤ : AddSubgroup (Fin 1 → ℤ)).map
      ((fun _ => (0 : (Fin 1 → ℤ) →+ (Fin 0 → ℤ))) (0 : Fin 1))) = 0 :=
    Module.finrank_zero_of_subsingleton
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, htop, hbot] at h1
  norm_num at h1

end MathlibExtTest.Combinatorics.DiscreteHolderBrascampLieb
