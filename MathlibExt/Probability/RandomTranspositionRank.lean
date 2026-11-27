/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomTranspositionFiltration
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Codimension bounds for the random-transposition symmetrisers

A sum over a right coset of the permutations supported in `R` only depends on the values of
the permutation outside `R`. The sums with complement of size `j` therefore have at most
`n.choose j * n ^ j` coordinates, including the non-injective assignments, whose fibres are empty.
This gives `finrank_quot_ker_symRankMap_le` without using a classification of representations.
The kernels can be characterised cumulatively (`mem_ker_symRankMap_iff_ge`) and are preserved by
the ordered-pair transposition sum (`transSum_mem_ker_symRankMap`).
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.RandomTranspositionFiltration

/-- A choice of `j` positions, together with the prescribed permutation values there. -/
abbrev SymRankCoord (n j : ℕ) :=
  Σ S : {S : Finset (Fin n) // S.card = j}, (↥S.val → Fin n)

/-- The sums over fibres of restriction of a permutation to a set of `j` positions. -/
noncomputable def symRankMap {n : ℕ} (j : ℕ) :
    (Equiv.Perm (Fin n) → ℝ) →ₗ[ℝ] (SymRankCoord n j → ℝ) where
  toFun f p := ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin n) => ∀ i : p.1.val, τ i = p.2 i), f τ
  map_add' f g := by ext p; simp [Finset.sum_add_distrib]
  map_smul' c f := by ext p; simp [Finset.mul_sum]

/-- Number of coordinates in the compressed family of symmetrisers. -/
theorem card_symRankCoord (n j : ℕ) :
    Fintype.card (SymRankCoord n j) = n.choose j * n ^ j := by
  classical
  unfold SymRankCoord
  rw [Fintype.card_sigma]
  calc
    _ = ∑ _S : {S : Finset (Fin n) // S.card = j}, n ^ j := by
      apply sum_congr rfl
      intro S _
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, S.property]
    _ = _ := by simp [Fintype.card_finset_len]

/-- Codimension of the simultaneous vanishing conditions on symmetrisers at complement size `j`.
For `j = 0` this is at most one. -/
theorem finrank_quot_ker_symRankMap_le (n j : ℕ) :
    Module.finrank ℝ ((Equiv.Perm (Fin n) → ℝ) ⧸ (symRankMap (n := n) j).ker) ≤
      n.choose j * n ^ j := by
  classical
  rw [(symRankMap (n := n) j).quotKerEquivRange.finrank_eq]
  exact (symRankMap (n := n) j).range.finrank_le.trans_eq
    ((Module.finrank_fintype_fun_eq_card ℝ).trans (card_symRankCoord n j))

private theorem symRankMap_apply_restrict {n j : ℕ} (S : Finset (Fin n)) (hS : S.card = j)
    (f : Equiv.Perm (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) :
    symRankMap j f ⟨⟨S, hS⟩, fun i => σ i⟩ = symSum Sᶜ f σ := by
  classical
  rw [symSum_eq_sum_agree]
  change (∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin n) => ∀ i : S, τ i = σ i), f τ) = _
  congr 1
  ext τ
  simp [Subtype.forall]

/-- The kernel of `symRankMap j` is exactly the simultaneous kernel of every symmetriser on a set
of size `n - j`. -/
theorem mem_ker_symRankMap_iff {n j : ℕ} (hj : j ≤ n) (f : Equiv.Perm (Fin n) → ℝ) :
    f ∈ (symRankMap j).ker ↔ ∀ R : Finset (Fin n), R.card = n - j → symSum R f = 0 := by
  classical
  rw [LinearMap.mem_ker]
  constructor
  · intro hf R hR
    have hc : Rᶜ.card = j := by rw [Finset.card_compl, Fintype.card_fin, hR]; omega
    ext σ
    have e := congrFun hf ⟨⟨Rᶜ, hc⟩, fun i => σ i⟩
    rwa [symRankMap_apply_restrict, compl_compl] at e
  · intro hf
    ext p
    obtain ⟨⟨S, hS⟩, v⟩ := p
    by_cases h : ∃ σ : Equiv.Perm (Fin n), ∀ i : S, σ i = v i
    · obtain ⟨σ, hσ⟩ := h
      have hv : v = fun i : ↥S => σ (i : Fin n) := (funext hσ).symm
      subst v
      rw [symRankMap_apply_restrict]
      exact congrFun (hf Sᶜ (by simp [Finset.card_compl, hS])) σ
    · change (∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin n) => ∀ i : S, τ i = v i), f τ) = 0
      have he : univ.filter (fun τ : Equiv.Perm (Fin n) => ∀ i : S, τ i = v i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        exact h ⟨τ, (Finset.mem_filter.mp hτ).2⟩
      rw [he, Finset.sum_empty]

/-- If all symmetrisers at size `s` vanish on `f`, so do the symmetrisers on larger sets. -/
theorem symSum_eq_zero_of_card_ge {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    {s : ℕ} {f : Equiv.Perm α → M}
    (hf : ∀ R : Finset α, R.card = s → symSum R f = 0)
    (R : Finset α) (hR : s ≤ R.card) : symSum R f = 0 := by
  induction R using Finset.induction_on with
  | empty => exact hf _ (by simpa [eq_comm] using hR)
  | insert a R ha ih =>
    by_cases he : (insert a R).card = s
    · exact hf _ he
    have hsmall : s ≤ R.card := by rw [card_insert_of_notMem ha] at hR he; omega
    funext σ
    rw [symSum_insert f σ ha, ih hsmall]
    simp

/-- Cumulative form of `mem_ker_symRankMap_iff`. -/
theorem mem_ker_symRankMap_iff_ge {n j : ℕ} (hj : j ≤ n) (f : Equiv.Perm (Fin n) → ℝ) :
    f ∈ (symRankMap j).ker ↔ ∀ R : Finset (Fin n), n - j ≤ R.card → symSum R f = 0 := by
  rw [mem_ker_symRankMap_iff hj f]
  exact ⟨fun hf => symSum_eq_zero_of_card_ge hf, fun hf R hR => hf R hR.ge⟩

/-- The ordered-pair transposition sum preserves the kernel of the level-`j` symmetrisers. -/
theorem transSum_mem_ker_symRankMap {n j : ℕ} (hj : j ≤ n) {f : Equiv.Perm (Fin n) → ℝ}
    (hf : f ∈ (symRankMap j).ker) : transSum univ f ∈ (symRankMap j).ker := by
  apply (mem_ker_symRankMap_iff hj _).mpr
  intro R hR
  rw [← transSum_symSum_comm (subset_univ R) f, (mem_ker_symRankMap_iff hj f).mp hf R hR]
  funext σ
  simp [transSum]

end MathlibExt.Probability.RandomTranspositionFiltration
