/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue

/-!
# Exact recovery by basis pursuit and the restricted nullspace property

In noiseless sparse regression one observes `y = X θ*` with `θ*` supported on a set `S` and
recovers `θ*` by **basis pursuit**, the linear program `min {‖θ‖₁ | X θ = y}`. Following
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge University
Press, 2019), §7.2.2, and Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*
(CRC Press, 2015), §10.4.1:

* `RestrictedNullspace X S`: the restricted nullspace property, `null(X) ∩ C(S; 1) = {0}`
  (Wainwright 2019, §7.2.2; Hastie et al. 2015, Definition 10.1).
* `basisPursuit_unique_iff_restrictedNullspace`: basis pursuit recovers every vector supported
  on `S`, as its unique solution, if and only if `X` has the restricted nullspace property over
  `S` (Wainwright 2019, §7.2.2; Hastie et al. 2015, Theorem 10.1 with Exercise 10.4).

"`θ*` is the unique solution of basis pursuit with `y = X θ*`" is written as: every `θ` with
`X θ = X θ*` and `‖θ‖₁ ≤ ‖θ*‖₁` equals `θ*`.

The equivalence is uniform over the vectors supported on `S`. Hastie et al. 2015, Theorem 10.1,
is stated for a fixed `θ*` that is the unique sparsest solution; read that way, only its "if"
direction holds, and the test module checks a counterexample to the fixed-`θ*` reading of the
converse. Hastie et al. 2015, Exercise 10.4, which proves the converse, assumes recovery of all
vectors supported on `S`, which is the uniform statement formalized here.
-/

open Finset Matrix

namespace MathlibExt.Probability.Statistics.BasisPursuit

open MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue

@[expose] public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The restricted nullspace property of a design matrix `X` over a set `S` of coordinates: the
only vector of the nullspace of `X` in the cone `C(S; 1) = {Δ | ‖Δ_{Sᶜ}‖₁ ≤ ‖Δ_S‖₁}` is `0`
(Wainwright, *High-Dimensional Statistics*, 2019, §7.2.2; Hastie, Tibshirani and
Wainwright, *Statistical Learning with Sparsity*, 2015, Definition 10.1). -/
def RestrictedNullspace (X : Matrix (Fin n) ι ℝ) (S : Finset ι) : Prop :=
  ∀ Δ : ι → ℝ, X *ᵥ Δ = 0 → Δ ∈ cone S 1 → Δ = 0

/-- **Exact recovery by basis pursuit** (Wainwright, *High-Dimensional Statistics*, 2019, §7.2.2;
Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*, 2015, Theorem 10.1, with
the converse in the uniform form of Exercise 10.4): the following are equivalent for a design
matrix `X` and a set `S` of coordinates.
(a) For every `θ*` vanishing off `S`, `θ*` is the unique solution of basis pursuit
`min {‖θ‖₁ | X θ = X θ*}`: every `θ` with `X θ = X θ*` and `‖θ‖₁ ≤ ‖θ*‖₁` equals `θ*`.
(b) `X` satisfies the restricted nullspace property over `S`. -/
theorem basisPursuit_unique_iff_restrictedNullspace (X : Matrix (Fin n) ι ℝ) (S : Finset ι) :
    (∀ θs : ι → ℝ, (∀ j ∉ S, θs j = 0) →
        ∀ θ : ι → ℝ, X *ᵥ θ = X *ᵥ θs → ∑ j, |θ j| ≤ ∑ j, |θs j| → θ = θs) ↔
      RestrictedNullspace X S := by
  constructor
  · -- Split a nullspace vector in the cone into its part on `S` and minus its part off `S`.
    intro h Δ hXΔ hcone
    set θs : ι → ℝ := fun j => if j ∈ S then Δ j else 0 with hθs
    set θ : ι → ℝ := fun j => if j ∈ S then 0 else -Δ j with hθ
    have hsupp : ∀ j ∉ S, θs j = 0 := fun j hj => by simp [hθs, hj]
    have hdiff : θs - θ = Δ := by
      funext j; by_cases hj : j ∈ S <;> simp [hθs, hθ, hj]
    have hX : X *ᵥ θ = X *ᵥ θs := by
      have : X *ᵥ θs - X *ᵥ θ = 0 := by rw [← mulVec_sub, hdiff, hXΔ]
      exact (sub_eq_zero.mp this).symm
    have hl1θ : ∑ j, |θ j| = ∑ j ∈ Sᶜ, |Δ j| := by
      rw [← sum_add_sum_compl S]
      have h1 : ∑ j ∈ S, |θ j| = 0 := sum_eq_zero fun j hj => by simp [hθ, hj]
      have h2 : ∑ j ∈ Sᶜ, |θ j| = ∑ j ∈ Sᶜ, |Δ j| :=
        sum_congr rfl fun j hj => by simp [hθ, mem_compl.mp hj]
      rw [h1, h2, zero_add]
    have hl1θs : ∑ j, |θs j| = ∑ j ∈ S, |Δ j| := by
      rw [← sum_add_sum_compl S]
      have h1 : ∑ j ∈ S, |θs j| = ∑ j ∈ S, |Δ j| := sum_congr rfl fun j hj => by simp [hθs, hj]
      have h2 : ∑ j ∈ Sᶜ, |θs j| = 0 :=
        sum_eq_zero fun j hj => by simp [hθs, mem_compl.mp hj]
      rw [h1, h2, add_zero]
    have hle : ∑ j, |θ j| ≤ ∑ j, |θs j| := by
      rw [hl1θ, hl1θs]
      have := hcone
      simp only [cone, Set.mem_ofPred_eq, one_mul] at this
      exact this
    have heq := h θs hsupp θ hX hle
    rw [← hdiff, heq, sub_self]
  · -- A feasible `θ` with smaller `ℓ₁` norm differs from `θ*` by a nullspace vector in the cone.
    intro hRN θs hsupp θ hX hle
    set Δ := θ - θs with hΔ
    have hXΔ : X *ᵥ Δ = 0 := by rw [hΔ, mulVec_sub, hX, sub_self]
    have hcone : Δ ∈ cone S 1 := by
      simp only [cone, Set.mem_ofPred_eq, one_mul]
      have hsplit : ∀ f : ι → ℝ, ∑ j, |f j| = ∑ j ∈ S, |f j| + ∑ j ∈ Sᶜ, |f j| :=
        fun f => (sum_add_sum_compl S _).symm
      have h0 : ∑ j ∈ Sᶜ, |θs j| = 0 :=
        sum_eq_zero fun j hj => by simp [hsupp j (mem_compl.mp hj)]
      have h1 : ∑ j ∈ Sᶜ, |θ j| = ∑ j ∈ Sᶜ, |Δ j| :=
        sum_congr rfl fun j hj => by simp [hΔ, hsupp j (mem_compl.mp hj)]
      have h2 : ∑ j ∈ S, |θs j| ≤ ∑ j ∈ S, |θ j| + ∑ j ∈ S, |Δ j| := by
        rw [← sum_add_distrib]
        refine sum_le_sum fun j _ => ?_
        calc |θs j| = |θ j + (-(θ j - θs j))| := by ring_nf
          _ ≤ |θ j| + |-(θ j - θs j)| := abs_add_le _ _
          _ = |θ j| + |Δ j| := by rw [abs_neg]; rfl
      rw [hsplit θ, hsplit θs, h0, h1] at hle
      linarith
    have := hRN Δ hXΔ hcone
    rw [hΔ] at this
    exact sub_eq_zero.mp this

end

end MathlibExt.Probability.Statistics.BasisPursuit
