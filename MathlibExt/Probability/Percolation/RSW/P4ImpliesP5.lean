/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RSW.ExpDecayUpgrade
public import MathlibExt.Probability.Percolation.RSW.P5Equivalences

/-!
# From "no exponential decay" (`P4`) to the box-crossing property (`P5`), abstractly

In the Duminil-Copin–Tassion dichotomy, a submultiplicative sequence `a n` (e.g. one-arm or
crossing probabilities) either decays stretched-exponentially, or the box-crossing property holds.
Since a submultiplicative sequence with stretched-exponential decay decays exponentially
(`StatMech.RSW.ExpDecay.rxd_exp_decay_of_stretched`), the failure of exponential decay (`P4`)
rules out the first branch. This file proves that propositional step; the dichotomy itself is the
hypothesis `hdich` of `rp4_p4_implies_p5`.

## Main definitions

* `StatMech.RSW.P4ImpliesP5.rp4_StretchedExpDecay`, `rp4_ExpDecay`, `rp4_P4`.

## Main results

* `StatMech.RSW.P4ImpliesP5.rp4_expDecay_of_stretched`: for submultiplicative `a`, stretched
  exponential decay implies exponential decay.
* `StatMech.RSW.P4ImpliesP5.rp4_p4_implies_p5`: `P4`, the dichotomy `hdich` and the chain bound
  `hchain` give `P5`.

## References

* H. Duminil-Copin, V. Tassion, *RSW and box-crossing property for planar percolation*,
  Proceedings of the International Congress of Mathematical Physics (2015).
-/

@[expose] public section

open Real Filter

namespace StatMech

namespace RSW

namespace P4ImpliesP5

open StatMech.RSW.Box

/-- Stretched-exponential decay: `a n ≤ exp (-n ^ α)` for some `α > 0`. -/
def rp4_StretchedExpDecay (a : ℕ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))

/-- Exponential decay: `a n ≤ C exp (-c n)` for some `c, C > 0`. -/
def rp4_ExpDecay (a : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, a n ≤ C * Real.exp (-c * n)

/-- Property `P4`: the sequence `a` does not decay exponentially. -/
def rp4_P4 (a : ℕ → ℝ) : Prop := ¬ rp4_ExpDecay a

/-- A submultiplicative, antitone sequence in `[0, 1]` with stretched-exponential decay decays
exponentially. -/
theorem rp4_expDecay_of_stretched (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hstr : rp4_StretchedExpDecay a) :
    rp4_ExpDecay a := by
  obtain ⟨α, hα, hbound⟩ := hstr
  obtain ⟨c, hc, C, hC, hdecay⟩ :=
    ExpDecay.rxd_exp_decay_of_stretched a hnn hle1 hanti α hα hbound hsub
  exact ⟨c, hc, C, hC, hdecay⟩

/-- Under `P4`, a submultiplicative sequence has no stretched-exponential decay. -/
theorem rp4_not_stretched_of_P4 (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hP4 : rp4_P4 a) :
    ¬ rp4_StretchedExpDecay a :=
  fun hstr => hP4 (rp4_expDecay_of_stretched a hnn hle1 hanti hsub hstr)

/-- `P4 → P5`, abstractly: if the submultiplicative sequence `a` does not decay exponentially and
the dichotomy `hdich` (`P5b` or stretched-exponential decay of `a`) holds, then `P5` holds for
`lam`. The dichotomy `hdich` is the Duminil-Copin–Tassion theorem and is assumed; `hchain` is the
same uniform-in-`α` hypothesis as in `StatMech.RSW.Box.rp5_p5b_p5_lower`, which genuine Bernoulli
measures with `0 < p < 1` do not satisfy (see `StatMech.RSW.Box.rp5_p5_equiv`). -/
theorem rp4_p4_implies_p5 (a : ℕ → ℝ)
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))) → ℝ}
    {lam : ℕ → Set (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))) → ℝ}
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hP4 : rp4_P4 a)
    (hdich : rp5_P5b ν ∨ rp4_StretchedExpDecay a)
    (hchain : ∀ (α : ℝ) (n : ℕ),
      ν 2 n (annulusEvent n) ≤ lam n (boxCrossingEvent α n)) :
    P5 lam := by
  have hnotstr : ¬ rp4_StretchedExpDecay a :=
    rp4_not_stretched_of_P4 a hnn hle1 hanti hsub hP4
  have hP5b : rp5_P5b ν := hdich.resolve_right hnotstr
  exact rp5_p5b_p5_lower hchain hP5b

end P4ImpliesP5

end RSW

end StatMech
