/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern

import Mathlib.Tactic

@[expose] public section

/-!
# The Allais paradox violates the independence axiom

The prizes are USD 0, USD 1 million and USD 5 million (`Fin 3`). The four Allais lotteries are
written as mixtures with weight `0.11` (`mix` from
`MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern`): `L₁` and `L₂` share the common
consequence USD 1M with weight `0.89`, `L₃` and `L₄` share USD 0, and the remaining weight `0.11`
is the sure USD 1M (`L₁`, `L₃`) or the risky lottery `riskyPart` (USD 0 w.p. `1/11`, USD 5M w.p.
`10/11`; in `L₂`, `L₄`). Independence (`SatisfiesIndependence`) forces `L₁ ≿ L₂ ↔ L₃ ≿ L₄`, so the
commonly observed pattern `L₁ ≻ L₂`, `L₄ ≻ L₃` violates it. A preference ranking lotteries by a
value that is quadratic in the probability of USD 1M shows the pattern is compatible with
completeness and transitivity.

## Main results

* `not_satisfiesIndependence_of_allais`: the Allais pattern violates independence.
* `exists_isPreferenceRelation_allais`: some complete transitive preference has the pattern.

## References

* M. Allais, "Le comportement de l'homme rationnel devant le risque: critique des postulats et
  axiomes de l'école américaine", Econometrica 21 (1953), 503--546.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 6.B (the Allais paradox).
-/

namespace MathlibExt.Economics.ExpectedUtility.Allais

open Convexity MathlibExt.Economics.ExpectedUtility

/-- Prizes of the Allais experiment: `0` is USD 0, `1` is USD 1 million, `2` is USD 5 million. -/
abbrev Prize := Fin 3

/-- The common risky component: USD 0 with probability `1/11`, USD 5M with probability `10/11`. -/
noncomputable def riskyPart : StdSimplex ℝ Prize :=
  StdSimplex.duple 0 2 (s := 1 / 11) (t := 10 / 11) (by norm_num) (by norm_num) (by norm_num)

/-- Allais lottery `L₁`: USD 1M for sure (written as `0.11 · δ_{1M} + 0.89 · δ_{1M}`). -/
noncomputable def L1 : StdSimplex ℝ Prize :=
  mix (11 / 100) (by norm_num) (by norm_num) (StdSimplex.single 1) (StdSimplex.single 1)

/-- Allais lottery `L₂`: USD 0 w.p. `0.01`, USD 1M w.p. `0.89`, USD 5M w.p. `0.10`
(written as `0.11 · riskyPart + 0.89 · δ_{1M}`). -/
noncomputable def L2 : StdSimplex ℝ Prize :=
  mix (11 / 100) (by norm_num) (by norm_num) riskyPart (StdSimplex.single 1)

/-- Allais lottery `L₃`: USD 0 w.p. `0.89`, USD 1M w.p. `0.11`
(written as `0.11 · δ_{1M} + 0.89 · δ_{0}`). -/
noncomputable def L3 : StdSimplex ℝ Prize :=
  mix (11 / 100) (by norm_num) (by norm_num) (StdSimplex.single 1) (StdSimplex.single 0)

/-- Allais lottery `L₄`: USD 0 w.p. `0.90`, USD 5M w.p. `0.10`
(written as `0.11 · riskyPart + 0.89 · δ_{0}`). -/
noncomputable def L4 : StdSimplex ℝ Prize :=
  mix (11 / 100) (by norm_num) (by norm_num) riskyPart (StdSimplex.single 0)

/-- Helper: weights of the risky component. -/
private lemma risky_w0 : riskyPart.weights (0 : Prize) = (1 / 11 : ℝ) := by
  unfold riskyPart
  rw [StdSimplex.weights_duple]
  simp

private lemma risky_w1 : riskyPart.weights (1 : Prize) = (0 : ℝ) := by
  unfold riskyPart
  rw [StdSimplex.weights_duple]
  simp

private lemma risky_w2 : riskyPart.weights (2 : Prize) = (10 / 11 : ℝ) := by
  unfold riskyPart
  rw [StdSimplex.weights_duple]
  simp

private lemma single1_w0 :
    ((StdSimplex.single 1 : StdSimplex ℝ Prize)).weights (0 : Prize) = (0 : ℝ) := by
  rw [StdSimplex.weights_single]; simp

private lemma single1_w1 :
    ((StdSimplex.single 1 : StdSimplex ℝ Prize)).weights (1 : Prize) = (1 : ℝ) := by
  rw [StdSimplex.weights_single]; simp

private lemma single1_w2 :
    ((StdSimplex.single 1 : StdSimplex ℝ Prize)).weights (2 : Prize) = (0 : ℝ) := by
  rw [StdSimplex.weights_single]; simp

private lemma single0_w0 :
    ((StdSimplex.single 0 : StdSimplex ℝ Prize)).weights (0 : Prize) = (1 : ℝ) := by
  rw [StdSimplex.weights_single]; simp

private lemma single0_w1 :
    ((StdSimplex.single 0 : StdSimplex ℝ Prize)).weights (1 : Prize) = (0 : ℝ) := by
  rw [StdSimplex.weights_single]; simp

private lemma single0_w2 :
    ((StdSimplex.single 0 : StdSimplex ℝ Prize)).weights (2 : Prize) = (0 : ℝ) := by
  rw [StdSimplex.weights_single]; simp

private lemma weights_mix (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (p q : StdSimplex ℝ Prize) (i : Prize) :
    (mix α h0 h1 p q).weights i = α * p.weights i + (1 - α) * q.weights i := by
  rw [mix_weights]
  simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

private lemma L1_w0 : L1.weights (0 : Prize) = (0 : ℝ) := by
  unfold L1; rw [weights_mix, single1_w0]; norm_num

private lemma L1_w1 : L1.weights (1 : Prize) = (1 : ℝ) := by
  unfold L1; rw [weights_mix, single1_w1]; norm_num

private lemma L1_w2 : L1.weights (2 : Prize) = (0 : ℝ) := by
  unfold L1; rw [weights_mix, single1_w2]; norm_num

lemma L2_w0 : L2.weights (0 : Prize) = (1 / 100 : ℝ) := by
  unfold L2; rw [weights_mix, risky_w0, single1_w0]; norm_num

lemma L2_w1 : L2.weights (1 : Prize) = (89 / 100 : ℝ) := by
  unfold L2; rw [weights_mix, risky_w1, single1_w1]; norm_num

lemma L2_w2 : L2.weights (2 : Prize) = (1 / 10 : ℝ) := by
  unfold L2; rw [weights_mix, risky_w2, single1_w2]; norm_num

private lemma L3_w0 : L3.weights (0 : Prize) = (89 / 100 : ℝ) := by
  unfold L3; rw [weights_mix, single1_w0, single0_w0]; norm_num

private lemma L3_w1 : L3.weights (1 : Prize) = (11 / 100 : ℝ) := by
  unfold L3; rw [weights_mix, single1_w1, single0_w1]; norm_num

private lemma L3_w2 : L3.weights (2 : Prize) = (0 : ℝ) := by
  unfold L3; rw [weights_mix, single1_w2, single0_w2]; norm_num

lemma L4_w0 : L4.weights (0 : Prize) = (9 / 10 : ℝ) := by
  unfold L4; rw [weights_mix, risky_w0, single0_w0]; norm_num

private lemma L4_w1 : L4.weights (1 : Prize) = (0 : ℝ) := by
  unfold L4; rw [weights_mix, risky_w1, single0_w1]; norm_num

lemma L4_w2 : L4.weights (2 : Prize) = (1 / 10 : ℝ) := by
  unfold L4; rw [weights_mix, risky_w2, single0_w2]; norm_num

/-- Nonlinear value function witnessing the Allais pattern. -/
private noncomputable def V (p : StdSimplex ℝ Prize) : ℝ :=
  p.weights 1 + 6 / 5 * p.weights 2 + 1 / 10 * (p.weights 1) ^ 2

/-- **The Allais pattern violates independence.** Any lottery preference that strictly prefers
the sure USD 1M (`L₁ ≻ L₂`) while strictly preferring the long shot `L₄ ≻ L₃` fails the independence
axiom. -/
theorem not_satisfiesIndependence_of_allais {R : StdSimplex ℝ Prize → StdSimplex ℝ Prize → Prop}
    (h12 : StrictPref R L1 L2) (h43 : StrictPref R L4 L3) : ¬ SatisfiesIndependence R := by
  intro hInd
  have h0 : (0 : ℝ) < 11 / 100 := by norm_num
  have h1 : (11 / 100 : ℝ) ≤ 1 := by norm_num
  have hiff1 : R (StdSimplex.single (1 : Prize)) riskyPart ↔ R L1 L2 := hInd _ _ _ _ h0 h1
  have hiff2 : R (StdSimplex.single (1 : Prize)) riskyPart ↔ R L3 L4 := hInd _ _ _ _ h0 h1
  have hSR : R (StdSimplex.single (1 : Prize)) riskyPart := hiff1.mpr h12.1
  have h34 : R L3 L4 := hiff2.mp hSR
  exact h43.2 h34

/-- The Allais pattern is consistent with completeness and transitivity: some preference
relation exhibits it (so `not_satisfiesIndependence_of_allais` is not vacuous). -/
theorem exists_isPreferenceRelation_allais :
    ∃ R : StdSimplex ℝ Prize → StdSimplex ℝ Prize → Prop,
      IsPreferenceRelation R ∧ StrictPref R L1 L2 ∧ StrictPref R L4 L3 := by
  refine ⟨fun p q => V q ≤ V p, ?_, ?_, ?_⟩
  · constructor
    · intro p q
      unfold V
      rcases le_total (p.weights 1 + 6 / 5 * p.weights 2 + 1 / 10 * (p.weights 1) ^ 2)
        (q.weights 1 + 6 / 5 * q.weights 2 + 1 / 10 * (q.weights 1) ^ 2) with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro p q r h1 h2
      exact le_trans h2 h1
  · constructor
    · change V L2 ≤ V L1
      unfold V
      rw [L1_w1, L1_w2, L2_w1, L2_w2]
      norm_num
    · change ¬ V L1 ≤ V L2
      unfold V
      rw [L1_w1, L1_w2, L2_w1, L2_w2]
      norm_num
  · constructor
    · change V L3 ≤ V L4
      unfold V
      rw [L3_w1, L3_w2, L4_w1, L4_w2]
      norm_num
    · change ¬ V L4 ≤ V L3
      unfold V
      rw [L3_w1, L3_w2, L4_w1, L4_w2]
      norm_num

end MathlibExt.Economics.ExpectedUtility.Allais
