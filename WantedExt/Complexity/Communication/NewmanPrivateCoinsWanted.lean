/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.CommunicationComplexity.Randomized

/-!
# Newman's theorem: public coins versus private coins

A public-coin protocol (`PublicCoinProtocol`) lets Alice and Bob read a shared random string.
In a private-coin protocol each party only sees its own random string: we model it as a
deterministic protocol in which Alice holds `(x, a)` and Bob holds `(y, b)`, with `a` and `b`
independent and uniform on finite sets. Newman's theorem says that public coins save at most
`log₂(n / ε²) + O(1)` bits on `n`-bit inputs, at the price of doubling the error
(I. Newman, "Private vs. common random bits in communication complexity", Inform. Process. Lett.
39 (1991); stated as Theorem 3.5 in A. Rao and A. Yehudayoff, *Communication Complexity*,
early draft).
-/

@[expose] public section

namespace MathlibExt.Computability.CommunicationComplexity

/-- **Error probability of a private-coin protocol.** For a deterministic protocol `p` in which
Alice holds `(x, a)` and Bob holds `(y, b)`, with nonempty finite sets `RA` and `RB` of private
random strings, the fraction of pairs `(a, b) ∈ RA × RB` on which `p` outputs a value other than
`f x y`: the probability of an error when `a` and `b` are independent and uniform. For an empty
set, which is excluded, every event would get probability `0`. -/
noncomputable def privateErrorProb {X Y RA RB : Type*} [Fintype RA] [Fintype RB] [Nonempty RA]
    [Nonempty RB] (p : Protocol (X × RA) (Y × RB)) (f : X → Y → Bool) (x : X) (y : Y) : ℚ :=
  ((Finset.univ.filter fun r : RA × RB => p.eval (x, r.1) (y, r.2) ≠ f x y).card : ℚ) /
    (Fintype.card RA * Fintype.card RB)

/-- **Newman's theorem.** There is a constant `C₀` such that for every `n ≥ 1` and
`0 < ε ≤ 1 / 2`: if
`g : {0,1}^n × {0,1}^n → {0,1}` is computed by a public-coin protocol (with a nonempty finite
set of random strings) of cost `c` and error at most `ε` on every input, then it is computed by
a private-coin protocol, with nonempty finite sets of private random strings, of cost at most
`c + log₂(n / ε²) + C₀` and error at most `2ε` on every input (A. Rao and A. Yehudayoff,
*Communication Complexity*, early draft, Theorem 3.5, attributed there to Newman, 1991). The
source leaves the range of `ε` implicit; its proof samples `O(n / ε²)` random strings, and some
upper bound on `ε` is needed: for large `ε` a cost-0 protocol meets the hypothesis while
`log₂(n / ε²)` is negative. -/
theorem_wanted newman_private_coins :
    ∃ C₀ : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (g : (Fin n → Bool) → (Fin n → Bool) → Bool) (R : Type) [Fintype R] [Nonempty R]
        (P : PublicCoinProtocol (Fin n → Bool) (Fin n → Bool) R),
        (∀ x y, (P.errorProb g x y : ℝ) ≤ ε) →
        ∃ (RA RB : Type) (_ : Fintype RA) (_ : Fintype RB) (_ : Nonempty RA) (_ : Nonempty RB)
          (p : Protocol ((Fin n → Bool) × RA) ((Fin n → Bool) × RB)),
          (p.depth : ℝ) ≤ P.cost + Real.logb 2 (n / ε ^ 2) + C₀ ∧
            ∀ x y, (privateErrorProb p g x y : ℝ) ≤ 2 * ε

end MathlibExt.Computability.CommunicationComplexity
