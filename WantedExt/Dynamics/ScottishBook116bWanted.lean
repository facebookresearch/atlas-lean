/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

open scoped ENNReal Topology

namespace MathlibExt.Dynamics.ScottishBook116bWanted

/-- The fair-coin measure on `Bool`: mass `1 / 2` on each of `false`, `true`. -/
noncomputable def coinFlip : MeasureTheory.Measure Bool :=
  (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac true

instance : MeasureTheory.IsProbabilityMeasure coinFlip :=
  ⟨by
    have h : coinFlip Set.univ = 1 := by
      simp only [coinFlip, MeasureTheory.Measure.add_apply,
        MeasureTheory.Measure.smul_apply, smul_eq_mul,
        MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ false),
        MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ true), mul_one,
        ← two_mul]
      rw [one_div]
      exact ENNReal.mul_inv_cancel (a := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    exact h⟩

/-- Fair-coin product measure on 0-1 sequences: the infinite product of
`coinFlip` over `ℕ`. -/
noncomputable def coinMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => coinFlip

/-- The `n`-th chosen generator: `phi` if `c n = false`, `psi` if
`c n = true`. Index `0` corresponds to `f_1` in the typescript. -/
def step {G : Type*} (phi psi : G) (c : ℕ → Bool) (n : ℕ) : G :=
  if c n then psi else phi

/-- Successive products `f_1`, `f_1 f_2`, `f_1 f_2 f_3`, ...:
`partialProd 0 = 1` is the empty product; `partialProd (n + 1)` is the
product of the first `n + 1` factors. The typescript writes the terms
as `f_1, f_1(f_2), f_1(f_2 f_3), ...`, read as successive products. -/
def partialProd {G : Type*} [Group G] (phi psi : G) (c : ℕ → Bool) : ℕ → G
  | 0 => 1
  | n + 1 => partialProd phi psi c n * step phi psi c n

/-- Scottish Book Problem 116, part (b): for almost every pair
`(phi, psi)` (Haar measure on `G × G`) generating an everywhere dense
subgroup, and almost every 0-1 sequence
`{c_n}` (fair-coin product measure), the successive products are
uniformly dense: for every measurable region `V`, the proportion
`q_n / n` of the first `n` partial products lying in `V` tends to the
Haar measure of `V`. "Region" is read as a measurable set, since the
typescript does not specify a class of regions and a measure is only
defined for measurable sets. The count uses the first `n` partial
products, i.e. indices `0, ..., n - 1`. -/
def ScottishBookProblem116bClaim : Prop :=
  ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G)
    [MeasureTheory.Measure.IsHaarMeasure μ] [MeasureTheory.IsProbabilityMeasure μ],
    ∀ᵐ p ∂(μ.prod μ),
      Dense ((Subgroup.closure {p.1, p.2} : Subgroup G) : Set G) →
        ∀ᵐ c ∂coinMeasure,
          ∀ V : Set G, MeasurableSet V →
        Filter.Tendsto
          (fun N : ℕ =>
            ((@Finset.filter ℕ (fun n => partialProd p.1 p.2 c n ∈ V)
              (fun _n => Classical.propDecidable _) (Finset.range N)).card : ℝ) / (N : ℝ))
          Filter.atTop (𝓝 (μ V).toReal)

/--
Scottish Book Problem 116, part (b) is false as stated.
Counterexample: take `G = S¹` with normalized Haar (Lebesgue) measure.
For this `G`, a.e. pair `(φ, ψ)` generates a dense subgroup, so the
`Dense` antecedent holds on a full-measure set of `p`. Fix any such
`p` and any `c`, and let `V_c = Set.range (partialProd p.1 p.2 c)`.
`V_c` is countable (the image of `ℕ`), hence measurable, and
`μ V_c = 0` (countable subsets of `S¹` have Lebesgue measure `0`).
Every partial product lies in `V_c`, so the counted frequency is
`N / N = 1` for every `N ≥ 1`, hence tends to `1`, not to
`(μ V_c).toReal = 0`. So the `∀ V` clause is false for every `c`,
hence the `∀ᵐ c` clause fails for every dense-generating `p`. The
quantifier order matters: `V` is quantified after `∀ᵐ c`, so `V` may
depend on the path `c`, and the only restriction on `V` is
`MeasurableSet V`; there is no frontier / continuity / Jordan
condition in the statement. The continuity-set version (restricting
to `V` with `μ (frontier V) = 0`) is a distinct proposition, filed
separately as `OpenConjectures.Dynamics.ScottishBook116bContinuitySets`.
Source: J. Schreier and S. Ulam, Problem 116, part (b) of the
Scottish Book, typescript PDF p. 56, printed p. 53; see the commentary
in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted scottishBook116b_refuted : ¬ ScottishBookProblem116bClaim

end MathlibExt.Dynamics.ScottishBook116bWanted
