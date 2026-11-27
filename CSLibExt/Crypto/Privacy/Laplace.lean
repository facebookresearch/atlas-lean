/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.Basic
public import MathlibExt.Probability.Distributions.Laplace

/-!
# The Laplace mechanism

The Laplace mechanism releases `f x` plus Laplace noise of scale `Δ / ε`, where `Δ` bounds the
sensitivity of `f` (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014,
Definitions 3.1 and 3.3). The scale must be positive, so every output law is a probability
measure (`isProbabilityMeasure_laplaceMechanism`): the mechanism always releases a sample. The
Laplace distribution itself is `MathlibExt.Probability.Distributions.Laplace`; the privacy proof
rests on `ProbabilityTheory.laplaceMeasure_le_smul`.

* `laplaceMechanism_differentiallyPrivate` (Dwork and Roth, 2014, Theorem 3.6, for real-valued
  queries): if `|f x - f y| ≤ Δ` on neighbours, the Laplace mechanism with scale `Δ / ε` is
  `ε`-differentially private.
* `laplaceMechanism_pi_differentiallyPrivate` (Theorem 3.6 for `f : X → ℝ^k` with
  `ℓ₁`-sensitivity at most `Δ`): independent noise on each coordinate; proved by applying the
  composition theorem `differentiallyPrivate_pi` to the two databases, coordinate by coordinate,
  with the privacy loss `|f x i - f y i| / b` of each coordinate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace Cslib.Crypto.Privacy

/-- **Laplace mechanism.** For a scale `b > 0`, release `f x + Y` with `Y` Laplace noise of
scale `b`, i.e. the law `laplaceMeasure (f x) b` (Dwork and Roth, 2014, Definition 3.3, for
real-valued `f`, with `b = Δf / ε`). The scale must be positive: every output law is then a
probability measure (`isProbabilityMeasure_laplaceMechanism`), whereas for `b ≤ 0` the truncated
density would vanish and the mechanism would release nothing. -/
noncomputable def laplaceMechanism {X : Type*} (f : X → ℝ) (b : ℝ) (_hb : 0 < b) :
    X → Measure ℝ :=
  fun x ↦ laplaceMeasure (f x) b

/-- **The Laplace mechanism releases a sample.** Every output law of the Laplace mechanism, whose
scale is positive, is a probability measure (Dwork and Roth, 2014, Definitions 3.2 and 3.3). -/
instance isProbabilityMeasure_laplaceMechanism {X : Type*} (f : X → ℝ) {b : ℝ} (hb : 0 < b)
    (x : X) : IsProbabilityMeasure (laplaceMechanism f b hb x) :=
  isProbabilityMeasure_laplaceMeasure hb (f x)

/-- **The Laplace mechanism is differentially private.** Let `f : X → ℝ` satisfy
`|f x - f y| ≤ Δ` whenever `Adj x y` (`Δ` bounds the sensitivity of `f`), with `Δ > 0` and
`ε > 0`. Then the Laplace mechanism with scale `Δ / ε > 0` is `ε`-differentially private (Dwork
and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Theorem 3.6, for
real-valued queries). -/
theorem laplaceMechanism_differentiallyPrivate {X : Type*} {Adj : X → X → Prop} {f : X → ℝ}
    {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (hf : ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ Δ) :
    DifferentiallyPrivate Adj (laplaceMechanism f (Δ / ε) (div_pos hΔ hε)) ε 0 := by
  have hb : 0 < Δ / ε := div_pos hΔ hε
  rw [differentiallyPrivate_zero_iff_le_smul]
  intro x y hxy
  simp only [laplaceMechanism]
  refine (laplaceMeasure_le_smul hb (f x) (f y)).trans ?_
  gcongr
  rw [div_le_iff₀ hb, mul_div_cancel₀ _ hε.ne']
  exact hf hxy

/-- **The Laplace mechanism for vector-valued queries.** Let `f : X → (Fin k → ℝ)` have
`ℓ₁`-sensitivity at most `Δ`, i.e. `∑ i, |f x i - f y i| ≤ Δ` whenever `Adj x y`, with `Δ > 0`
and `ε > 0`. Adding independent Laplace noise of scale `Δ / ε` to each coordinate is
`ε`-differentially private (Dwork and Roth, *The Algorithmic Foundations of Differential
Privacy*, 2014, Definition 3.3 and Theorem 3.6). -/
theorem laplaceMechanism_pi_differentiallyPrivate {X : Type*} {Adj : X → X → Prop} {k : ℕ}
    {f : X → Fin k → ℝ} {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε)
    (hf : ∀ ⦃x y⦄, Adj x y → ∑ i, |f x i - f y i| ≤ Δ) :
    DifferentiallyPrivate Adj (fun x ↦ Measure.pi fun i ↦ laplaceMeasure (f x i) (Δ / ε)) ε 0 := by
  have hb : 0 < Δ / ε := div_pos hΔ hε
  intro x y hxy S hS
  -- the two databases as a two-point space, one coordinate at a time
  let M' : ∀ _ : Fin k, Bool → Measure ℝ :=
    fun i a ↦ laplaceMeasure (f (if a then x else y) i) (Δ / ε)
  have : ∀ i a, IsProbabilityMeasure (M' i a) := fun _ _ ↦
    isProbabilityMeasure_laplaceMeasure hb _
  have hi : ∀ i, DifferentiallyPrivate (fun a a' : Bool ↦ a = true ∧ a' = false) (M' i)
      (|f x i - f y i| / (Δ / ε)) 0 := by
    intro i
    rw [differentiallyPrivate_zero_iff_le_smul]
    rintro a a' ⟨rfl, rfl⟩
    exact laplaceMeasure_le_smul hb _ _
  have key := differentiallyPrivate_pi (Ω := fun _ : Fin k ↦ ℝ) hi (x := true) (y := false)
    ⟨rfl, rfl⟩ S hS
  simp only [M', ite_true, Bool.false_eq_true, ite_false, Finset.sum_const_zero,
    add_zero] at key
  rw [add_zero]
  refine key.trans ?_
  dsimp only
  gcongr
  rw [← Finset.sum_div, div_le_iff₀ hb, mul_div_cancel₀ _ hε.ne']
  exact hf hxy

end Cslib.Crypto.Privacy
