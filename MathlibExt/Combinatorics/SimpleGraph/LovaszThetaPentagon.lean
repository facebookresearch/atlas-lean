/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaStrongPower
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Lovász's umbrella: `ϑ(C₅) ≤ √5` and the Shannon capacity of the pentagon

Lovász labels the five vertices of the pentagon by the ribs of an umbrella in `ℝ³`: ribs
`(h, cos (2πk / 5), sin (2πk / 5))` at angles `2πk / 5` around the axis, whose common height `h`
makes the ribs two steps apart orthogonal. Against the handle `e₀` every cost is `1 / √5`, so
`ϑ(C₅) ≤ √5`, and by Lovász's bound `Θ(G) ≤ ϑ(G)` the Shannon capacity of the pentagon is at most
`√5`. (The matching lower bound `Θ(C₅) ≥ √5` comes from the five-element independent set
`{(i, 2i)}` of `C₅ ⊠ C₅`; it is not formalised here.)

Source: L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979),
1-7.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

open scoped RealInnerProductSpace
open Real

/-- **Cosines of the pentagon's long diagonals.** For `m ∈ {±2, ±3}`,
`cos (2π m / 5) = -(1 + √5) / 4`, from `cos (π / 5) = (1 + √5) / 4`. -/
theorem cos_two_pi_mul_div_five {m : ℤ} (hm : m = 2 ∨ m = 3 ∨ m = -2 ∨ m = -3) :
    cos (2 * π * m / 5) = -((1 + √5) / 4) := by
  rw [← cos_pi_div_five]
  rcases hm with rfl | rfl | rfl | rfl
  · rw [show 2 * π * ((2 : ℤ) : ℝ) / 5 = π - π / 5 by push_cast; ring, cos_pi_sub]
  · rw [show 2 * π * ((3 : ℤ) : ℝ) / 5 = π / 5 + π by push_cast; ring, cos_add_pi]
  · rw [show 2 * π * ((-2 : ℤ) : ℝ) / 5 = -(π - π / 5) by push_cast; ring, cos_neg, cos_pi_sub]
  · rw [show 2 * π * ((-3 : ℤ) : ℝ) / 5 = -(π / 5 + π) by push_cast; ring, cos_neg, cos_add_pi]

/-- **Height of Lovász's umbrella.** `h = √((1 + √5) / 4)`, chosen so that the ribs of the
umbrella at angle `4π / 5` are orthogonal: `h² + cos (4π / 5) = 0`. -/
noncomputable def umbrellaHeight : ℝ := √((1 + √5) / 4)

/-- **Square of the umbrella height.** `h · h = (1 + √5) / 4`. -/
theorem umbrellaHeight_sq : umbrellaHeight * umbrellaHeight = (1 + √5) / 4 :=
  Real.mul_self_sqrt (by positivity)

/-- **Lovász's umbrella.** The labeling of the pentagon `C₅` by the vectors
`(h, cos (2πk / 5), sin (2πk / 5)) ∈ ℝ³`, `k ∈ ℤ/5` (Lovász, "On the Shannon capacity of a graph",
IEEE Trans. Inform. Theory 25 (1979), the umbrella construction; Knuth, *The Sandwich Theorem*,
1994, §22 treats odd cycles). -/
noncomputable def umbrella (k : Fin 5) : EuclideanSpace ℝ (Fin 3) :=
  !₂[umbrellaHeight, cos (2 * π * k / 5), sin (2 * π * k / 5)]

/-- **Inner products of the umbrella ribs.**
`⟪u_j, u_k⟫ = (1 + √5) / 4 + cos (2π (j - k) / 5)`. -/
theorem inner_umbrella (j k : Fin 5) :
    ⟪umbrella j, umbrella k⟫ =
      (1 + √5) / 4 + cos (2 * π * (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) / 5) := by
  simp only [umbrella, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Int.cast_sub,
    Int.cast_natCast]
  rw [umbrellaHeight_sq]
  rw [show 2 * π * ((j : ℝ) - k) / 5 = 2 * π * j / 5 - 2 * π * k / 5 by ring, cos_sub]
  ring


/-- **Non-adjacent vertices of the pentagon.** Two distinct non-adjacent vertices `u, v` of `C₅`
satisfy `u - v ∈ {±2, ±3}` as integers. -/
theorem cycleGraph_five_nonadj_diff {u v : Fin 5} (huv : u ≠ v)
    (hadj : ¬ (SimpleGraph.cycleGraph 5).Adj u v) :
    ((u : ℤ) - v) = 2 ∨ ((u : ℤ) - v) = 3 ∨ ((u : ℤ) - v) = -2 ∨ ((u : ℤ) - v) = -3 := by
  rw [SimpleGraph.cycleGraph_adj] at hadj
  revert u v
  decide

/-- **The umbrella certifies `√5`.** The umbrella is an orthogonal labeling of `C₅` all of whose
costs, against the handle `e₀`, equal `1 / √5`; so `√5` is a feasible value of the theta program for
the pentagon (Lovász 1979). -/
theorem sqrt_five_mem_thetaFeasible_cycleGraph_five :
    √5 ∈ thetaFeasible (SimpleGraph.cycleGraph 5) := by
  have h5 : (0 : ℝ) < √5 := by positivity
  have hs5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  refine ⟨h5.le, 3, umbrella, EuclideanSpace.single 0 1, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h
    simp at this
  · intro u v huv hadj
    rw [inner_umbrella, cos_two_pi_mul_div_five (cycleGraph_five_nonadj_diff huv hadj)]
    ring
  · intro v
    have hin : ⟪EuclideanSpace.single 0 (1 : ℝ), umbrella v⟫ = umbrellaHeight := by
      rw [EuclideanSpace.inner_single_left]
      simp [umbrella]
    have hnorm : ‖umbrella v‖ ^ 2 = (1 + √5) / 4 + 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_umbrella]
      simp
    have hsq : umbrellaHeight ^ 2 = (1 + √5) / 4 := by rw [sq]; exact umbrellaHeight_sq
    simp only [cost, hin, hnorm, hsq, PiLp.norm_single, norm_one, one_pow, one_mul]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith

/-- **Theta of the pentagon is at most `√5`.** `ϑ(C₅) ≤ √5` (Lovász, "On the Shannon capacity of a
graph", IEEE Trans. Inform. Theory 25 (1979), where equality is proved). -/
theorem lovaszTheta_cycleGraph_five_le : lovaszTheta (SimpleGraph.cycleGraph 5) ≤ √5 :=
  csInf_le ⟨0, fun _ ht => ht.1⟩ sqrt_five_mem_thetaFeasible_cycleGraph_five

/-- **The Shannon capacity of the pentagon is at most `√5`.** If graphs `H k` on words
`Fin (k + 1) → Fin 5`, such as the strong powers of `C₅`, satisfy the hypothesis of
`pow_mem_thetaFeasible` and `α(H k)^(1/(k+1)) → θ`, then `θ ≤ √5` (Lovász, "On the Shannon
capacity of a graph", IEEE Trans. Inform. Theory 25 (1979), the upper half of `Θ(C₅) = √5`). -/
theorem le_sqrt_five_of_tendsto (H : ∀ k : ℕ, SimpleGraph (Fin (k + 1) → Fin 5))
    (hH : ∀ k x y, x ≠ y → ¬ (H k).Adj x y →
      ∃ i, x i ≠ y i ∧ ¬ (SimpleGraph.cycleGraph 5).Adj (x i) (y i)) {θ : ℝ}
    (hθ : Filter.Tendsto (fun k : ℕ => ((H k).indepNum : ℝ) ^ (((k : ℝ) + 1)⁻¹))
      Filter.atTop (nhds θ)) :
    θ ≤ √5 :=
  (le_lovaszTheta_of_tendsto _ H hH hθ).trans lovaszTheta_cycleGraph_five_le

end MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
