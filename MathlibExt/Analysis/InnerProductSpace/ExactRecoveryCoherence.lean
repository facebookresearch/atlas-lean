/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition

/-!
# Coherence implies the Exact Recovery Condition

The Exact Recovery Condition of `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition`
asks, for every atom `ψ` outside the optimal support, for coefficients `a` of the orthogonal
projection of `ψ` onto the span of the optimal atoms with `‖a‖₁ < 1`. J. A. Tropp (*Greed is
good: algorithmic results for sparse approximation*, IEEE Trans. Inform. Theory 50 (2004),
2231–2242, Theorem 3.5 and Corollary 3.6) shows that it holds for every support of size `m` as
soon as the dictionary is incoherent: if the atoms have unit norm and pairwise inner products at
most `μ` in modulus, then `(2m - 1) μ < 1`, that is `m < (μ⁻¹ + 1) / 2`, suffices. Then OMP and
basis pursuit recover every `m`-term superposition.

## Main declarations

* `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherenceWanted.exists_erc_of_coherence` :
  if `(2m - 1) μ < 1`, every atom `D ω` outside a support `Λ` of size `m` has coefficients `a`
  of its projection onto the span of the atoms of `Λ` with `∑ᵢ |aᵢ| < 1`.

## Proof outline

Tropp bounds the inverse of the Gram matrix of the optimal atoms through a Neumann series. The
argument here needs no inverse. Let `K` be the span of the atoms `D i`, `i ∈ Λ`, and let `a` be
coefficients of the projection, `∑ᵢ aᵢ D i = P_K (D ω)`; they exist because `P_K (D ω) ∈ K`.

* Since `D ω - P_K (D ω)` is orthogonal to `K`, the coefficients solve the normal equations
  `∑ᵢ aᵢ ⟪D j, D i⟫ = ⟪D j, D ω⟫` for `j ∈ Λ`.
* The diagonal coefficient is `⟪D j, D j⟫ = 1`, while the other coefficients and the right-hand
  side (`j ≠ ω`) are at most `μ` in modulus. With `S = ∑ᵢ |aᵢ|` this gives
  `|aⱼ| ≤ μ + μ (S - |aⱼ|)`.
* Summing over `j ∈ Λ` gives `S ≤ m μ + (m - 1) μ S`, that is `(1 - (m - 1) μ) S ≤ m μ`. The
  hypothesis says `m μ < 1 - (m - 1) μ`, and `μ ≥ 0` as soon as `Λ` is nonempty, so `S < 1`.

The bound holds for every choice of coefficients of `P_K (D ω)`, so the linear independence of
the optimal atoms (which also follows from `(2m - 1) μ < 1`) is not needed.

## Implementation notes

The theorem keeps the full name it had in the former wanted module, so its namespace still reads
`ExactRecoveryCoherenceWanted`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherenceWanted

/-- **Coherence implies the Exact Recovery Condition** (J. A. Tropp, *Greed is good: algorithmic
results for sparse approximation*, IEEE Trans. Inform. Theory 50 (2004), Theorem 3.5 with the
bound `μ₁(k) ≤ k μ`, as in Corollary 3.6). Let `D` be a dictionary of unit vectors in an inner
product space whose coherence is at most `μ`: `|⟨D i, D j⟩| ≤ μ` for `i ≠ j`. Let `Λ` be a finite
set of `m` indices with `(2m - 1) μ < 1`. Then for every index `ω ∉ Λ` there are coefficients
`a` with `∑_{i ∈ Λ} aᵢ D i = P_K (D ω)`, where `K` is the span of the atoms indexed by `Λ`, and
`∑_{i ∈ Λ} |aᵢ| < 1`. -/
theorem exists_erc_of_coherence {𝕜 E κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (D : κ → E) (hD : ∀ i, ‖D i‖ = 1) {μ : ℝ}
    (hμ : ∀ i j, i ≠ j → ‖⟪D i, D j⟫_𝕜‖ ≤ μ) (Λ : Finset κ)
    (hm : (2 * (Λ.card : ℝ) - 1) * μ < 1) {ω : κ} (hω : ω ∉ Λ) :
    ∃ a : Λ → 𝕜,
      ∑ i, a i • D i = (Submodule.span 𝕜 (Set.range fun i : Λ => D i)).starProjection (D ω) ∧
        ∑ i, ‖a i‖ < 1 := by
  classical
  set K := Submodule.span 𝕜 (Set.range fun i : Λ => D i)
  -- `P_K (D ω)` lies in `K`, so it has coefficients `a` in the atoms indexed by `Λ`.
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp
    (K.starProjection_apply_mem (D ω))
  refine ⟨a, ha, ?_⟩
  set S := ∑ i, ‖a i‖ with hS
  set m : ℝ := (Λ.card : ℝ)
  -- The coefficients solve the normal equations `∑ᵢ aᵢ ⟪D j, D i⟫ = ⟪D j, D ω⟫`, `j ∈ Λ`.
  have hnormal (j : Λ) : ∑ i, a i * ⟪D j, D i⟫_𝕜 = ⟪D (j : κ), D ω⟫_𝕜 := by
    have hjK : D j ∈ K := Submodule.subset_span ⟨j, rfl⟩
    calc ∑ i, a i * ⟪D j, D i⟫_𝕜 = ⟪D j, ∑ i, a i • D i⟫_𝕜 := by
          simp_rw [inner_sum, inner_smul_right]
      _ = ⟪D j, D ω⟫_𝕜 := by
          rw [ha, ← Submodule.inner_starProjection_left_eq_right,
            Submodule.starProjection_eq_self_iff.mpr hjK]
  -- The diagonal coefficient is `1`; the others and the right-hand side are at most `μ`.
  have hcoord (j : Λ) : ‖a j‖ ≤ μ + μ * (S - ‖a j‖) := by
    have hjj : ⟪D (j : κ), D j⟫_𝕜 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hD, RCLike.ofReal_one, one_pow]
    have hsplit := hnormal j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hjj, mul_one] at hsplit
    have hjω : (j : κ) ≠ ω := fun h => hω (h ▸ j.2)
    calc ‖a j‖ = ‖⟪D (j : κ), D ω⟫_𝕜 - ∑ i ∈ Finset.univ.erase j, a i * ⟪D j, D i⟫_𝕜‖ := by
          rw [← hsplit, add_sub_cancel_right]
      _ ≤ ‖⟪D (j : κ), D ω⟫_𝕜‖ + ∑ i ∈ Finset.univ.erase j, ‖a i * ⟪D j, D i⟫_𝕜‖ :=
          (norm_sub_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
      _ ≤ μ + ∑ i ∈ Finset.univ.erase j, ‖a i‖ * μ := by
          gcongr with i hi
          · exact hμ _ _ hjω
          · rw [norm_mul]
            gcongr
            exact hμ _ _ fun h => Finset.ne_of_mem_erase hi (Subtype.ext h).symm
      _ = μ + μ * (S - ‖a j‖) := by
          rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ j)]
          ring
  -- Summing over `j ∈ Λ` gives `S ≤ m μ + (m - 1) μ S`.
  have hsum : S ≤ m * μ + μ * (m * S - S) := by
    calc S ≤ ∑ j : Λ, (μ + μ * (S - ‖a j‖)) := Finset.sum_le_sum fun j _ => hcoord j
      _ = m * μ + μ * (m * S - S) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← hS]
          simp [m]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  rcases Λ.eq_empty_or_nonempty with hΛ | ⟨j, hj⟩
  · -- No optimal atoms: `m = 0`, and `S ≤ -μ S` with `-μ < 1` forces `S = 0`.
    have hm0 : m = 0 := by simp [m, hΛ]
    rw [hm0] at hsum hm
    nlinarith
  · -- Some optimal atom `D j` with `j ≠ ω`, so `0 ≤ |⟪D j, D ω⟫| ≤ μ`.
    have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ j ω fun h => hω (h ▸ hj))
    have hm1 : 1 ≤ m := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨j, hj⟩)
    by_contra hS1
    have hS1 : 1 ≤ S := not_lt.mp hS1
    nlinarith [mul_le_mul_of_nonneg_left hS1 (by nlinarith : (0 : ℝ) ≤ 1 - (m - 1) * μ)]

end MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherenceWanted
