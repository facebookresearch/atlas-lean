/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.InformationTheory.ChannelCodingStrongConverse
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Shannon's channel coding theorem for discrete memoryless channels: wishlist

A discrete memoryless channel with finite input alphabet `α` and finite output alphabet `β` is a
stochastic matrix `W : α → PMF β`, used `n` times independently. Its capacity, in bits, is
`C(W) = sup_p I(X; Y)` over input laws `p`, where `(X, Y)` has law `p(a) W(a)(b)`; below it is
written inline as `⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))`.
The input alphabet is assumed nonempty (otherwise no codeword exists). A deterministic code of
blocklength `n` with `M` messages is an encoder `f : Fin M → (Fin n → α)` and a decoder
`g : (Fin n → β) → Fin M` without an erasure output; message `m` is decoded wrongly with probability
`W^{⊗n}(· | f m){y | g y ≠ m}`, the product law `Measure.pi fun i => (W (f m i)).toMeasure`.

The coding theorem as Polyanskiy and Wu state it has three parts: every rate below capacity is
achievable with vanishing maximal error, every rate above capacity forces the average error to one
(strong converse), and Fano's inequality bounds every code at every blocklength (weak converse).
Achievability is proved, by Gallager's random coding bound, as
`MathlibExt.InformationTheory.ChannelCodingAchievability.channelCoding_achievability`. The strong
converse is proved in `MathlibExt.InformationTheory.ChannelCodingStrongConverse`. The book's codes
may be randomised and their decoders may output an erasure. Both converse statements specialize to
deterministic erasure-free codes.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025: Definition 19.2 (codes), Theorem 19.9 (Shannon), Corollary 19.5 (maximal error),
  Theorem 17.3 and Theorem 19.7 (weak converse), Theorem 22.1 (strong converse).
* C. E. Shannon, A mathematical theory of communication, Bell Syst. Tech. J. 27 (1948).
* J. Wolfowitz, The coding of messages subject to chance errors, Illinois J. Math. 1 (1957).
-/

namespace MathlibExt.InformationTheory.ChannelCodingWanted

@[expose] public section

open MeasureTheory _root_.InformationTheory

/-- **Weak converse** (Fano). For a discrete memoryless channel `W` on finite alphabets, every
code with `M ≥ 1` codewords of length `n` and average error probability `Pₑ` satisfies
`(1 - Pₑ) log₂ M ≤ n C(W) + h(Pₑ)`, where `h` is the binary entropy in bits.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 17.3 (`log M ≤ (sup I(X; Y) + h(ε)) / (1 - ε)`) applied to the
`n`-letter channel, with Proposition 19.10 (`sup I(Xⁿ; Yⁿ) = n C`), as in Theorem 19.7. -/
public theorem_wanted channelCoding_weak_converse {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [MeasurableSpace β] [DiscreteMeasurableSpace β] (W : α → PMF β) (n M : ℕ)
    (hM : 1 ≤ M) (f : Fin M → Fin n → α) (g : (Fin n → β) → Fin M) :
    let Pe : ℝ := (∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}) / M
    (1 - Pe) * Real.logb 2 M ≤
      n * (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) +
        Real.binEntropy Pe / Real.log 2

end

end MathlibExt.InformationTheory.ChannelCodingWanted
