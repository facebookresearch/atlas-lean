/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Tactic.LinearCombination

/-!
# Primitive elements `α + nβ` in a prime cyclotomic field

For a prime `p`, a `p`-th cyclotomic extension `K` of `ℚ`, and `α β : K`, the subfields
`ℚ(α + nβ)` and `ℚ(α, β)` of `K` are equal for all sufficiently large `n : ℕ`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Corollary 1.
-/

namespace MetaMathlibExt

open scoped Classical in
/-- Some `n` with `σ (α + nβ) = α + nβ` and `σ β ≠ β` if one exists, else `0`. -/
private noncomputable def badChoice {K : Type*} [Field K] [CharZero K] (α β : K)
    (σ : K ≃ₐ[ℚ] K) : ℕ :=
  if h : ∃ n : ℕ, σ β ≠ β ∧ σ (α + (n : K) * β) = α + (n : K) * β then
    Classical.choose h
  else 0

/-- At most one `n` makes `σ` fix `α + nβ` while moving `β`. -/
private theorem badChoice_uniq {K : Type*} [Field K] [CharZero K] {α β : K}
    (σ : K ≃ₐ[ℚ] K) (n₁ n₂ : ℕ) (hσ : σ β ≠ β)
    (h₁ : σ (α + (n₁ : K) * β) = α + (n₁ : K) * β)
    (h₂ : σ (α + (n₂ : K) * β) = α + (n₂ : K) * β) : n₁ = n₂ := by
  simp only [map_add, map_mul, map_natCast] at h₁ h₂
  have e₁ : σ α - α = (n₁ : K) * (β - σ β) := by linear_combination h₁
  have e₂ : σ α - α = (n₂ : K) * (β - σ β) := by linear_combination h₂
  have hEq : (n₁ : K) * (β - σ β) = (n₂ : K) * (β - σ β) := by rw [← e₁, ← e₂]
  have hne : β - σ β ≠ 0 := sub_ne_zero.mpr hσ.symm
  have hcast : (n₁ : K) = (n₂ : K) := mul_right_cancel₀ hne hEq
  exact Nat.cast_injective hcast

set_option linter.unusedVariables false in
/-- **Primitive elements α + nβ in a prime cyclotomic field.** Let $p$ be a prime and let $K$
be a $p$-th cyclotomic extension of $\mathbb{Q}$. For all $\alpha, \beta \in K$ there is a
natural number $n_0$ such that, for every natural number $n \ge n_0$, the subfields
$\mathbb{Q}(\alpha + n\beta)$ and $\mathbb{Q}(\alpha, \beta)$ of $K$ are equal.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Corollary 1 (`integers-2025-A10-cor-1`). -/
public theorem eventually_adjoin_add_nsmul_eq {p : ℕ} [NeZero p] {K : Type*}
    [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (α β : K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IntermediateField.adjoin ℚ {α + (n : K) * β} =
        IntermediateField.adjoin ℚ {α, β} := by
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  have : IsGaloisGroup (K ≃ₐ[ℚ] K) ℚ K := IsGaloisGroup.of_isGalois ℚ K
  let _ := Fintype.ofFinite (K ≃ₐ[ℚ] K)
  have fspec : ∀ σ : K ≃ₐ[ℚ] K, ∀ n : ℕ, σ β ≠ β →
      σ (α + (n : K) * β) = α + (n : K) * β → badChoice α β σ = n := by
    intro σ n hσ hcon
    have hex : ∃ m : ℕ, σ β ≠ β ∧ σ (α + (m : K) * β) = α + (m : K) * β :=
      ⟨n, hσ, hcon⟩
    have hspec := Classical.choose_spec hex
    simp only [badChoice]
    rw [dite_eq_left hex]
    exact badChoice_uniq σ _ n hσ hspec.2 hcon
  set s : Finset ℕ := Finset.univ.image (badChoice α β) with hs
  refine ⟨s.sup id + 1, fun n hn => ?_⟩
  have hmem : ∀ σ : K ≃ₐ[ℚ] K, σ β ≠ β →
      σ (α + (n : K) * β) ≠ α + (n : K) * β := by
    intro σ hσ hcon
    have hnmem : n ∈ s := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, fspec σ n hσ hcon⟩
    have hle : n ≤ s.sup id := by simpa using Finset.le_sup (f := id) hnmem
    omega
  have hle : IntermediateField.adjoin ℚ {α + (n : K) * β} ≤
      IntermediateField.adjoin ℚ {α, β} := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have hα : α ∈ IntermediateField.adjoin ℚ {α, β} :=
      IntermediateField.subset_adjoin ℚ {α, β} (by simp)
    have hβ : β ∈ IntermediateField.adjoin ℚ {α, β} :=
      IntermediateField.subset_adjoin ℚ {α, β} (by simp)
    have hnK : (n : K) ∈ IntermediateField.adjoin ℚ {α, β} :=
      IntermediateField.natCast_mem _ n
    exact add_mem hα (mul_mem hnK hβ)
  have hfix : fixingSubgroup (K ≃ₐ[ℚ] K)
      (↑(IntermediateField.adjoin ℚ {α + (n : K) * β}) : Set K) =
      fixingSubgroup (K ≃ₐ[ℚ] K) (↑(IntermediateField.adjoin ℚ {α, β}) : Set K) := by
    apply le_antisymm
    · intro σ hσ
      rw [mem_fixingSubgroup_iff] at hσ ⊢
      have hγmem : α + (n : K) * β ∈
          (↑(IntermediateField.adjoin ℚ {α + (n : K) * β}) : Set K) :=
        IntermediateField.subset_adjoin ℚ _ (by simp)
      have hγ : σ (α + (n : K) * β) = α + (n : K) * β := by
        have hsm := hσ _ hγmem
        simpa [AlgEquiv.smul_def] using hsm
      have hβ : σ β = β := by
        by_contra hne
        exact hmem σ hne hγ
      have hα : σ α = α := by
        have hγ' := hγ
        simp only [map_add, map_mul, map_natCast] at hγ'
        rw [hβ] at hγ'
        exact add_right_cancel hγ'
      intro y hy
      rw [AlgEquiv.smul_def]
      refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hy
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hα
        · exact hβ
      · intro q
        exact σ.commutes q
      · intro x y hx hy hxeq hyeq
        rw [map_add, hxeq, hyeq]
      · intro x hx hxeq
        rw [map_inv₀, hxeq]
      · intro x y hx hy hxeq hyeq
        rw [map_mul, hxeq, hyeq]
    · exact IsGaloisGroup.fixingSubgroup_le_of_le _ _ _ _ _ hle
  have h1 := IsGaloisGroup.fixedPoints_fixingSubgroup (K ≃ₐ[ℚ] K) ℚ K
    (IntermediateField.adjoin ℚ {α + (n : K) * β})
  have h2 := IsGaloisGroup.fixedPoints_fixingSubgroup (K ≃ₐ[ℚ] K) ℚ K
    (IntermediateField.adjoin ℚ {α, β})
  rw [hfix] at h1
  rw [h2] at h1
  exact h1.symm

end MetaMathlibExt
