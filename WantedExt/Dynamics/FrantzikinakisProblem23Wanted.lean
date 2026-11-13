/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiple ergodic averages problem 23
-/
module

public import Mathlib
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Dynamics.FrantzikinakisProblem23Wanted

/-! Source record `AMR-047-0023__4800023`. -/

open scoped BigOperators

/-!
# Clause inventory for [AMR-047-0023]

Source: Frantzikinakis — Some open problems on multiple ergodic averages (2016),
Problem 23, https://arxiv.org/abs/1103.3808.

Enumerated hypotheses, side conditions, and quantifier domains formalized below:
(a) `ℓ : ℕ` and `a : Fin ℓ → (ℝ → ℝ)` is the family `ℱ = {a₁, …, aℓ}`;
(b) all `a i` lie in one Hardy field `H : Set (ℝ → ℝ)`;
(c) `H` contains constants and is closed under addition and multiplication;
(d) `H` is closed under differentiation at infinity;
(e) each `a i` has polynomial growth at infinity;
(f) `span^*(ℱ)` means `∑ i, w i * a i` with `w : Fin ℓ → ℝ`, `∃ i, w i ≠ 0`;
(g) for every such combination, every `c : ℝ`, every `p : Polynomial ℤ`,
    `|∑ i, w i * a i t - c * p(t)| / Real.log t → ∞` as `t → ∞`;
(h) `X : Type*` with `[MeasurableSpace X]` and `μ : MeasureTheory.Measure X`
    with `[MeasureTheory.IsProbabilityMeasure μ]`;
(i) `T : Equiv.Perm X` is the ergodic invertible transformation;
(j) every integer power `⇑(T ^ k)` is measurable;
(k) every integer power preserves `μ`;
(l) `T`-invariant measurable sets have measure `0` or `1` (ergodicity);
(m) `f : Fin ℓ → (X → ℝ)` with `MeasureTheory.MemLp (f i) ⊤ μ` (`L∞(μ)`);
(n) `[·]` is `Int.floor`, applied to `a i (n : ℝ)`;
(o) averages `(N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ∏ i, f i ((T ^ ⌊a i n⌋) x)`;
(p) limit is `∏ i, MeasureTheory.integral μ (f i)` with convergence in `L²(μ)`,
    i.e. `eLpNorm` with `(2 : ENNReal)` of the difference tends to `0`.
-/

/-- Frantzikinakis Problem 23 [AMR-047-0023]: multiple ergodic averages along a
Hardy-field family of polynomial growth. Source: Frantzikinakis, Some open
problems on multiple ergodic averages (2016), Problem 23,
https://arxiv.org/abs/1103.3808. Posed there as an open problem and since solved by
Tsinas (see `conjecture_holds` below); the declaration states the implication as a
proposition. -/
def conjecture : Prop :=
  ∀ (ℓ : ℕ) (a : Fin ℓ → (ℝ → ℝ)),
    (∃ H : Set (ℝ → ℝ), (∀ i, a i ∈ H) ∧
      (∀ c : ℝ, (fun _ => c) ∈ H) ∧
      (∀ f g : ℝ → ℝ, f ∈ H → g ∈ H → f + g ∈ H) ∧
      (∀ f g : ℝ → ℝ, f ∈ H → g ∈ H → f * g ∈ H) ∧
      (∀ f : ℝ → ℝ, f ∈ H → ∃ f' : ℝ → ℝ, f' ∈ H ∧
        Filter.Eventually (fun t => HasDerivAt f (f' t) t) Filter.atTop) ∧
      (∀ f : ℝ → ℝ, f ∈ H →
        (∀ᶠ t in Filter.atTop, f t = 0) ∨
        (∀ᶠ t in Filter.atTop, 0 < f t) ∨
        (∀ᶠ t in Filter.atTop, f t < 0)) ∧
      (∀ f : ℝ → ℝ, f ∈ H → (∀ᶠ t in Filter.atTop, f t ≠ 0) →
        ∃ g : ℝ → ℝ, g ∈ H ∧ ∀ᶠ t in Filter.atTop, f t * g t = 1) ∧
      (∀ i, ∃ C : ℝ, ∃ n : ℕ, Filter.Eventually
        (fun t => |a i t| ≤ C * t ^ n) Filter.atTop)) →
    (∀ w : Fin ℓ → ℝ, (∃ i, w i ≠ 0) →
      ∀ (c : ℝ) (p : Polynomial ℤ),
        Filter.Tendsto
          (fun t => |∑ i, w i * a i t - c * ((p.map (Int.castRingHom ℝ)).eval t)| /
            Real.log t)
          Filter.atTop Filter.atTop) →
    ∀ (X : Type*) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsProbabilityMeasure μ] (T : Equiv.Perm X),
      (∀ k : ℤ, Measurable ⇑(T ^ k)) →
      (∀ k : ℤ, ∀ s : Set X, MeasurableSet s →
        μ (⇑(T ^ k) ⁻¹' s) = μ s) →
      (∀ s : Set X, MeasurableSet s → ⇑T ⁻¹' s = s → μ s = 0 ∨ μ s = 1) →
      ∀ (f : Fin ℓ → (X → ℝ)),
        (∀ i, MeasureTheory.MemLp (f i) ⊤ μ) →
        Filter.Tendsto
          (fun N : ℕ =>
            MeasureTheory.eLpNorm
              (fun x =>
                ((N : ℝ)⁻¹ *
                  ∑ n ∈ Finset.Icc 1 N,
                    ∏ i, f i ((T ^ (Int.floor (a i (n : ℝ)))) x) -
                ∏ i, MeasureTheory.integral μ (f i)))
              (2 : ENNReal) μ)
          Filter.atTop (nhds 0)

/--
Resolved true: Resolved affirmatively by Tsinas (Joint ergodicity of Hardy field sequences,
Trans. Amer. Math. Soc. 376 (2023) 3191-3263, arXiv:2109.07941): if all nontrivial linear
combinations of the Hardy-field functions stay logarithmically away from rational polynomials,
the L^2 limit of the averages equals the product of the integrals in ergodic systems.
Frantzikinakis's progress page (November 2025) marks Problem 23 solved by Tsinas. Source: K.
Tsinas, Joint ergodicity of Hardy field sequences, Trans. Amer. Math. Soc. 376 (2023) 3191-3263,
arXiv:2109.07941, https://arxiv.org/abs/2109.07941. Moved from
`OpenConjectures/Dynamics/FrantzikinakisProblem23`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Dynamics.FrantzikinakisProblem23Wanted
