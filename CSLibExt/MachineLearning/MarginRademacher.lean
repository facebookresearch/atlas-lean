/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.RademacherComplexity

/-!
# Rademacher complexity of the margin costs of voting classifiers

The structural step of the margin bounds for voting methods (Schapire, Freund, Bartlett and Lee,
*Boosting the margin*, Ann. Statist. 26, 1998, Section 2, for the setting). It combines the
analogues, in the convention of `rademacherComplexity`, of Bartlett and Mendelson's Theorem 12,
part 2 (the convex hull) and part 4 (Lipschitz composition) (*Rademacher and Gaussian
complexities*, JMLR 3, 2002); the result bounds the complexity term `2 L R_n(F)` of their margin
bound, Theorem 7, when `F` is a convex hull:
on a fixed sample with labels `yᵢ ∈ {±1}`, let `B ⊆ ℝⁿ` be the value vectors of the base
classifiers. A voting classifier `f = ∑ₕ aₕ h` (`aₕ ≥ 0`, `∑ aₕ = 1`) has its value vector in
the convex hull of `B`, and its margins on the sample are `yᵢ f(xᵢ)`. For a cost `φ` that is
`L`-Lipschitz, the Rademacher complexity of the margin costs `(φ(yᵢ f(xᵢ)))ᵢ` of all voting
classifiers is at most `L` times that of the base classifiers alone: the convex hull is free
(`rademacherComplexity_convexHull`) and composing with the cost multiplies the complexity by at
most its Lipschitz constant (`rademacherComplexity_coordMap_le`). The size of the vote never enters.

The ramp `ρ_θ` (`ramp`) is the usual cost: it dominates the zero-one loss `1[u ≤ 0]`, is
dominated by the margin error `1[u ≤ θ]`, and is `1 / θ`-Lipschitz, so the complexity term of a
margin bound for voting classifiers is `R(B) / θ`.

Main results:

* `rademacherComplexity_marginCosts_convexHull_le`: `R(φ ∘ margins of conv B) ≤ L R(B)`.
* `ramp`, `indicator_le_ramp`, `ramp_le_indicator`, `lipschitzWith_ramp`.
* `rademacherComplexity_rampCosts_convexHull_le`: `R(ρ_θ ∘ margins of conv B) ≤ R(B) / θ`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Rademacher

variable {n : ℕ}

/-- **The margin cost vectors** `(φ(yᵢ aᵢ))ᵢ` of the value vectors `a ∈ A`, for labels `y`. -/
def marginCosts (φ : ℝ → ℝ) (y : Fin n → ℝ) (A : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (fun a i => φ (y i * a i)) '' A

/-- **The margin costs of voting classifiers are no more complex than the base classifiers**
(Bartlett and Mendelson, *JMLR* 3, 2002, Theorem 12, parts 2 and 4, combined, in the convention
of `rademacherComplexity`: `rademacherComplexity_convexHull` and the contraction lemma
`rademacherComplexity_coordMap_le`; it bounds the complexity term of their margin bound, Theorem 7,
for a convex hull): for a nonempty bounded `B ⊆ ℝⁿ`, labels with `|yᵢ| ≤ 1` and an
`L`-Lipschitz cost `φ`, `R({(φ(yᵢ aᵢ))ᵢ : a ∈ conv B}) ≤ L R(B)`. -/
theorem rademacherComplexity_marginCosts_convexHull_le {B : Set (Fin n → ℝ)} (hne : B.Nonempty)
    (hB : Bornology.IsBounded B) (φ : ℝ → ℝ) {L : NNReal} (hφ : LipschitzWith L φ)
    (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    rademacherComplexity (marginCosts φ y (convexHull ℝ B)) ≤ L * rademacherComplexity B := by
  have hconv : Bornology.IsBounded (convexHull ℝ B) := isBounded_convexHull.2 hB
  have hlip : ∀ i, LipschitzWith L (fun x => φ (y i * x)) := by
    intro i
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    calc dist (φ (y i * x)) (φ (y i * x')) ≤ L * dist (y i * x) (y i * x') :=
          hφ.dist_le_mul _ _
      _ = L * (|y i| * dist x x') := by rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      _ ≤ L * (1 * dist x x') := by gcongr; exact hy i
      _ = L * dist x x' := by ring
  have h := rademacherComplexity_coordMap_le hconv (fun i x => φ (y i * x)) hlip
  rw [rademacherComplexity_convexHull hne hB] at h
  exact h

/-- **The ramp cost** `ρ_θ(u) = min 1 (max 0 (1 - u / θ))`: `1` for `u ≤ 0`, `0` for `u ≥ θ`, linear
in between. -/
noncomputable def ramp (θ u : ℝ) : ℝ := min 1 (max 0 (1 - u / θ))

private theorem ramp_nonneg (θ u : ℝ) : 0 ≤ ramp θ u :=
  le_min zero_le_one (le_max_left _ _)

private theorem ramp_le_one (θ u : ℝ) : ramp θ u ≤ 1 := min_le_left _ _

/-- **The ramp dominates the zero-one loss**: `1[u ≤ 0] ≤ ρ_θ(u)` for `θ > 0`. -/
theorem indicator_le_ramp {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    (if u ≤ 0 then (1 : ℝ) else 0) ≤ ramp θ u := by
  split_ifs with hu
  · have : 1 ≤ 1 - u / θ := by
      have : u / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hθ.le
      linarith
    exact le_min le_rfl (le_max_of_le_right this)
  · exact ramp_nonneg θ u

/-- **The ramp is dominated by the margin error**: `ρ_θ(u) ≤ 1[u ≤ θ]` for `θ > 0`. -/
theorem ramp_le_indicator {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    ramp θ u ≤ if u ≤ θ then (1 : ℝ) else 0 := by
  split_ifs with hu
  · exact ramp_le_one θ u
  · have : 1 - u / θ ≤ 0 := by
      have : 1 ≤ u / θ := (one_le_div hθ).2 (le_of_not_ge hu)
      linarith
    exact (min_le_right _ _).trans (max_le le_rfl this)

/-- **The ramp `ρ_θ` is `1 / θ`-Lipschitz** for `θ > 0`. -/
theorem lipschitzWith_ramp {θ : ℝ} (hθ : 0 < θ) :
    LipschitzWith (Real.toNNReal θ⁻¹) (ramp θ) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_pos.2 hθ).le]
  calc |ramp θ u - ramp θ v|
      ≤ max |1 - 1| |max 0 (1 - u / θ) - max 0 (1 - v / θ)| := abs_min_sub_min_le_max _ _ _ _
    _ = |max 0 (1 - u / θ) - max 0 (1 - v / θ)| := by simp
    _ ≤ max |0 - 0| |(1 - u / θ) - (1 - v / θ)| := abs_max_sub_max_le_max _ _ _ _
    _ = θ⁻¹ * |u - v| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _),
          show (1 - u / θ) - (1 - v / θ) = -(θ⁻¹ * (u - v)) by ring, abs_neg, abs_mul,
          abs_of_pos (inv_pos.2 hθ)]

/-- **The complexity term of the margin bound for voting classifiers**: for a nonempty bounded
`B ⊆ ℝⁿ` of base-classifier value vectors, labels with `|yᵢ| ≤ 1` and `θ > 0`, the ramp costs of
the margins of all voting classifiers satisfy `R({(ρ_θ(yᵢ aᵢ))ᵢ : a ∈ conv B}) ≤ R(B) / θ`
(Bartlett and Mendelson, *JMLR* 3, 2002, Theorem 12, parts 2 and 4, in the convention of
`rademacherComplexity`, with the `1 / θ`-Lipschitz ramp; this is the complexity term of their
Theorem 7 with `L = 1 / θ`). -/
theorem rademacherComplexity_rampCosts_convexHull_le {B : Set (Fin n → ℝ)} (hne : B.Nonempty)
    (hB : Bornology.IsBounded B) (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) {θ : ℝ} (hθ : 0 < θ) :
    rademacherComplexity (marginCosts (ramp θ) y (convexHull ℝ B)) ≤
      rademacherComplexity B / θ := by
  have h := rademacherComplexity_marginCosts_convexHull_le hne hB (ramp θ)
    (lipschitzWith_ramp hθ) y hy
  rw [Real.coe_toNNReal _ (inv_pos.2 hθ).le] at h
  rwa [div_eq_inv_mul]

end Cslib.MachineLearning.Rademacher
