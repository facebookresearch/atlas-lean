/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.BlackwellApproachability
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! # Blackwell's approachability theorem, almost-sure form

The expected-payoff form of Blackwell's theorem is proved in
`MathlibExt.GameTheory.BlackwellApproachability`
(`blackwell_expected_approachability`, rate `M / √t`). Passing to realised payoffs needs a
strong law of large numbers for bounded martingale differences (Hart 2005, Appendix, footnote 38;
Blackwell 1956, Theorem 2), which is why the almost-sure statement is recorded here.

Randomised play is modelled on a probability space `(Ω, P)` by a process `Z : ℕ → Ω → α` of
realised actions; the conditional law of the next round given the history `Z 0, …, Z t` is
written with conditional expectations of indicators with respect to `historySigma Z t`.

## References

* D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6
  (1956), 1–8, Theorem 1.
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: Appendix, Theorem 5.
* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: §3, Blackwell's Approachability Theorem.
-/

namespace MathlibExt.GameTheory.BlackwellApproachabilityWanted

open MeasureTheory Filter Topology Finset
open MathlibExt.GameTheory.BlackwellApproachability (average)

/-- The σ-algebra of the events determined by the history `Z 0, …, Z t` of a process (each
`Z k` carrying the discrete σ-algebra on its values). -/
@[instance_reducible]
def historySigma {Ω α : Type*} (Z : ℕ → Ω → α) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ k ≤ t, MeasurableSpace.comap (Z k) ⊤

/-- **Blackwell's approachability theorem** (Blackwell 1956, Theorem 1 and §3; Hart 2005,
Appendix, Theorem 5; Hart and Mas-Colell 2000, §3). Let `v : A → B → ℝᵈ` be a vector payoff with
finite action sets and `C` a nonempty closed convex set every closed half-space of which
containing `C` is enforceable. Then `C` is approachable: some strategy `σ` of the decision
maker, mapping the current average payoff to a mixed action (the Blackwell strategy), guarantees
that whatever the opponent does (randomising or not, independently of the decision maker's
current randomisation given the past) the average realised vector payoff converges to `C` almost
surely. The first round is arbitrary. -/
theorem_wanted blackwell_approachability {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (v : A → B → EuclideanSpace ℝ (Fin d)) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C)
    (henf : ∀ (lam : EuclideanSpace ℝ (Fin d)) (ρ : ℝ), (∀ c ∈ C, @inner ℝ _ _ lam c ≤ ρ) →
      ∃ q : Convexity.StdSimplex ℝ A, ∀ b, @inner ℝ _ _ lam (∑ a, q.weights a • v a b) ≤ ρ) :
    ∃ σ : EuclideanSpace ℝ (Fin d) → Convexity.StdSimplex ℝ A,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℕ → Ω → A × B), (∀ n z, MeasurableSet {ω | Z n ω = z}) →
        (∀ n a b,
          P[{ω | Z (n + 1) ω = (a, b)}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] =ᵐ[P]
            fun ω => (σ (average (fun k => v (Z k ω).1 (Z k ω).2) (n + 1))).weights a *
              P[{ω | (Z (n + 1) ω).2 = b}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] ω) →
        ∀ᵐ ω ∂P, Tendsto
          (fun n => Metric.infDist (average (fun k => v (Z k ω).1 (Z k ω).2) n) C) atTop (𝓝 0)

end MathlibExt.GameTheory.BlackwellApproachabilityWanted
