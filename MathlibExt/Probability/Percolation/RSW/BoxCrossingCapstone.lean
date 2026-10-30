/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RSW.P4ImpliesP5
public import MathlibExt.Probability.Percolation.RSW.P5Equivalences

/-!
# Uniform box-crossing property from `P4`, abstractly

Combines `StatMech.RSW.P4ImpliesP5.rp4_p4_implies_p5` with
`StatMech.RSW.Box.rp5_p5_equiv` to state the conclusion `P5c μ` (two-sided crossing bounds
uniform over a family of measures).

## Main results

* `StatMech.RSW.boxCrossing_uniform_of_p4_inputs`.

## Implementation notes

The hypothesis `htwo` of `boxCrossing_uniform_of_p4_inputs` is `P5c μ` itself, so the conclusion
holds by `htwo` alone and the other hypotheses play no logical role. The statement is kept as a
record of how the pieces are meant to compose; it proves nothing beyond `htwo`.
-/

@[expose] public section

namespace StatMech.RSW

open Box

/-- Composition of `P4 → P5` (`rp4_p4_implies_p5`) with `P5 ↔ P5c` (`rp5_p5_equiv`).

Fidelity: the hypothesis `htwo` is literally `P5c μ`, which is the conclusion; the theorem is
therefore trivial and carries no mathematical content beyond `htwo`. `hchain` is moreover not
satisfied by genuine Bernoulli measures with `0 < p < 1` (see `rp5_p5_equiv`). -/
theorem boxCrossing_uniform_of_p4_inputs {Ξ : Type*} (ξ₀ : Ξ)
    {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Lattice.Site 2))) → ℝ}
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Lattice.Site 2))) → ℝ}
    (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hP4 : P4ImpliesP5.rp4_P4 a)
    (hdich : rp5_P5b ν ∨ P4ImpliesP5.rp4_StretchedExpDecay a)
    (hcmp : ∀ R n, μ ξ₀ n (annulusEvent n) ≤ ν R n (annulusEvent n))
    (hglue : ∀ n, μ ξ₀ n (boxCrossingEvent 10 n) ^ 4 ≤ μ ξ₀ n (annulusEvent n))
    (hchain : ∀ α n, ν 2 n (annulusEvent n) ≤ μ ξ₀ n (boxCrossingEvent α n))
    (htwo : ∀ α, 0 < α → ∃ c, 0 < c ∧ ∀ ξ n,
      c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c) :
    P5c μ := by
  have hp5 : P5 (μ ξ₀) :=
    P4ImpliesP5.rp4_p4_implies_p5 a hnn hle1 hanti hsub hP4 hdich hchain
  exact (rp5_p5_equiv ξ₀ hcmp hglue hchain htwo).2.2.2.mp hp5

end StatMech.RSW
