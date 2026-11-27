/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CeaLemma

/-!
# Weak solutions from the Lax–Milgram theorem

The abstract form of the existence theory for the Dirichlet problem `-Δ u = f`, `u = 0` on `∂U`.
A real Hilbert space `H` plays the role of `H¹₀(U)`, a bounded linear map `D : H → G` into a real
inner product space plays the role of the gradient `u ↦ Du ∈ L²(U; ℝⁿ)`, and the Dirichlet form is
`B[u, v] = ⟪D u, D v⟫ = ∫_U Du · Dv`. A Poincaré-type bound `β ‖u‖² ≤ ‖D u‖²` makes `B` coercive,
so the Lax–Milgram theorem (Mathlib's `IsCoercive.continuousLinearEquivOfBilin`, packaged in
`MathlibExt.Analysis.InnerProductSpace.CeaLemma`) gives a unique weak solution of `B[u, v] = L v`
for every bounded linear functional `L` (for `-Δ u = f`, `L v = ∫_U f v`), with `‖u‖ ≤ ‖L‖ / β`.

For a symmetric nonnegative form, Dirichlet's principle identifies weak solutions with the
minimizers of the energy `B[w, w] / 2 - L w`.

The concrete Sobolev-space statement on a bounded open `U ⊆ ℝⁿ` is proved in
`MathlibExt.Analysis.PDE.PoissonDirichlet`.

## Main results

* `gradientForm`, `isCoercive_gradientForm`: the Dirichlet form and its coercivity.
* `existsUnique_weakSolution`: existence and uniqueness of the weak solution.
* `norm_le_of_weakSolution`: the energy estimate `‖u‖ ≤ ‖L‖ / β`.
* `isMinOn_energy_iff`: Dirichlet's principle.

## References

* P. Howard, *Second order elliptic PDE: the Lax–Milgram theorem*, MATH 612 lecture slides, Texas
  A&M University, Spring 2020, https://people.tamu.edu/~phoward/m612/s20/elliptic2.pdf: Theorem
  6.2.1 (the Lax–Milgram theorem, numbered after §6.2.1 of Evans,
  *Partial Differential Equations*, 2nd ed.) and its "Application to Poisson's equation".
* L. C. Evans, *Mathematics 195: Dynamic Optimization*, lecture notes, Spring 2021 version,
  https://math.berkeley.edu/~evans/, §3.2.1, Theorem 3.2.1 and the example of the functional
  `∫_U |∇u|²/2 - u f`, whose Euler–Lagrange equation is Poisson's equation `-Δ u = f`.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.WeakSolutions

open MathlibExt.Analysis.InnerProductSpace.CeaLemma
open scoped RealInnerProductSpace

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **Dirichlet form of a gradient operator.** For a bounded linear map `D : H → G` between real
inner product spaces, the bounded bilinear form `B[u, v] = ⟪D u, D v⟫`. With `H = H¹₀(U)` and `D`
the gradient into `L²(U; ℝⁿ)` this is `∫_U Du · Dv`, the form of the weak formulation of
Poisson's equation in P. Howard, MATH 612 slides *The Lax–Milgram theorem* (Texas A&M, 2020),
"Application to Poisson's equation". -/
noncomputable def gradientForm (D : H →L[ℝ] G) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ (E := G)).bilinearComp D D

@[simp]
theorem gradientForm_apply (D : H →L[ℝ] G) (u v : H) : gradientForm D u v = ⟪D u, D v⟫ := rfl

/-- **Poincaré-type bound gives coercivity.** If `β > 0` and `β ‖u‖² ≤ ‖D u‖²` for all `u`, then
the Dirichlet form `⟪D u, D v⟫` is coercive. For `H¹₀(U)` the bound follows from Poincaré's
inequality, as in P. Howard, MATH 612 slides *The Lax–Milgram theorem* (Texas A&M, 2020),
"Application to Poisson's equation", where `β = min(1/(2C²), 1/2)`. -/
theorem isCoercive_gradientForm {D : H →L[ℝ] G} {β : ℝ} (hβ : 0 < β)
    (hP : ∀ u, β * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) : IsCoercive (gradientForm D) :=
  ⟨β, hβ, fun u => by
    rw [gradientForm_apply, real_inner_self_eq_norm_sq, mul_assoc, ← sq]
    exact hP u⟩

/-- **Existence and uniqueness of weak solutions of the abstract Poisson problem.** Let `H` be a
real Hilbert space, `D : H → G` bounded linear with `β ‖u‖² ≤ ‖D u‖²` for some `β > 0`. Then for
every bounded linear functional `L` on `H` there is exactly one `u ∈ H` with `⟪D u, D v⟫ = L v`
for all `v ∈ H`. This is the abstract skeleton of the application of the Lax–Milgram theorem
(Theorem 6.2.1) to Poisson's equation in P. Howard, MATH 612 slides *The Lax–Milgram theorem*
(Texas A&M, 2020), obtained from the Lax–Milgram solution `variationalSolution`. -/
theorem existsUnique_weakSolution [CompleteSpace H] {D : H →L[ℝ] G} {β : ℝ} (hβ : 0 < β)
    (hP : ∀ u, β * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) (L : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v, ⟪D u, D v⟫ = L v := by
  have hB := isCoercive_gradientForm hβ hP
  refine ⟨variationalSolution hB L, fun v => variationalSolution_spec hB L v, fun w hw => ?_⟩
  exact variationalSolution_eq_of_forall hB hw

/-- **Energy estimate for the abstract Poisson problem.** Under the hypotheses of
`existsUnique_weakSolution`, the weak solution satisfies `‖u‖ ≤ ‖L‖ / β`, from
`β ‖u‖² ≤ ⟪D u, D u⟫ = L u ≤ ‖L‖ ‖u‖` (the stability bound of the Lax–Milgram solution,
`norm_variationalSolution_le`; P. Howard, MATH 612 slides *The Lax–Milgram theorem*, Texas A&M,
2020, proof of Theorem 6.2.1). -/
theorem norm_le_of_weakSolution [CompleteSpace H] {D : H →L[ℝ] G} {β : ℝ} (hβ : 0 < β)
    (hP : ∀ u, β * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) {L : H →L[ℝ] ℝ} {u : H}
    (hu : ∀ v, ⟪D u, D v⟫ = L v) : ‖u‖ ≤ ‖L‖ / β := by
  have hB := isCoercive_gradientForm hβ hP
  rw [variationalSolution_eq_of_forall hB hu]
  refine norm_variationalSolution_le hB L hβ fun v => ?_
  rw [gradientForm_apply, real_inner_self_eq_norm_sq, mul_assoc, ← sq]
  exact hP v

/-- **Dirichlet energy of a bilinear form and a load.** For a bounded bilinear form `B` and a
bounded linear functional `L`, the quadratic functional `I[w] = B[w, w] / 2 - L w`; for
`B[u, v] = ∫_U Du · Dv` and `L v = ∫_U f v` it is the functional `∫_U |∇w|²/2 - w f` of
L. C. Evans, *Math 195 lecture notes* (Spring 2021), §3.2.1. -/
noncomputable def energy (B : H →L[ℝ] H →L[ℝ] ℝ) (L : H →L[ℝ] ℝ) (w : H) : ℝ :=
  B w w / 2 - L w

/-- Expansion of the energy along a line through `u`. -/
private theorem energy_add_smul {B : H →L[ℝ] H →L[ℝ] ℝ} (hsymm : ∀ u v, B u v = B v u)
    (L : H →L[ℝ] ℝ) (u h : H) (s : ℝ) :
    energy B L (u + s • h) = energy B L u + s * (B u h - L h) + s ^ 2 / 2 * B h h := by
  simp only [energy, map_add, map_smul, FunLike.coe_add,
    FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsymm h u]
  ring

/-- **Dirichlet's principle.** Let `B` be a symmetric bounded bilinear form with `B[v, v] ≥ 0` for
all `v`. Then `u` minimizes the energy `B[w, w] / 2 - L w` if and only if `B[u, v] = L v` for all
`v`: minimizers are exactly the weak solutions. This is an abstract, two-sided version of the
first-variation argument of L. C. Evans, *Math 195 lecture notes* (Spring 2021), §3.2.1,
Theorem 3.2.1 (a `C²` minimizer solves the Euler–Lagrange equation) applied to the functional
`∫_U |∇u|²/2 - u f`, whose Euler–Lagrange equation is Poisson's equation. No coercivity is needed;
with coercivity, `existsUnique_weakSolution` gives the minimizer. -/
theorem isMinOn_energy_iff {B : H →L[ℝ] H →L[ℝ] ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hpos : ∀ v, 0 ≤ B v v) (L : H →L[ℝ] ℝ) (u : H) :
    (∀ w, energy B L u ≤ energy B L w) ↔ ∀ v, B u v = L v := by
  constructor
  · intro hmin v
    by_contra hne
    set a := B u v - L v with ha
    have ha0 : a ≠ 0 := sub_ne_zero.mpr hne
    set b := B v v
    have hb := hpos v
    have key := hmin (u + (-a / (b + 1)) • v)
    rw [energy_add_smul hsymm] at key
    have hb1 : 0 < b + 1 := by linarith
    have ha2 : 0 < a ^ 2 := by positivity
    have : (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 / 2 * b < 0 := by
      rw [div_pow, neg_sq]
      have e1 : (-a / (b + 1)) * a = -(a ^ 2 / (b + 1)) := by ring
      rw [e1]
      have e2 : a ^ 2 / (b + 1) ^ 2 / 2 * b ≤ a ^ 2 / (b + 1) / 2 := by
        rw [div_div, div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (b + 1)]
      have e3 : 0 < a ^ 2 / (b + 1) := by positivity
      linarith
    linarith
  · intro hsol w
    have := energy_add_smul hsymm L u (w - u) 1
    simp only [one_smul, add_sub_cancel, one_pow, hsol, sub_self, mul_zero,
      add_zero] at this
    rw [this]
    have := hpos (w - u)
    linarith

end MathlibExt.Analysis.PDE.WeakSolutions
