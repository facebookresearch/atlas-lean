# Law objective posterior match

The finite item law, the named expectation-maximization joint, and the
responsibilities agree.

For valid mixture parameters `θ`, an observation pattern `x`, and a latent
state `k`, all three of the following hold.

1. The locally independent item-response mass of `x` at the `k`-th
   component probabilities, read as a real number, is the product-Bernoulli
   mass `bernPMF` at those probabilities.
2. The named joint `joint θ`, summed over all observation patterns and all
   latent states, is `1`. This is summation over the full outcome space;
   it is not a sum over a data list.
3. Let `κ` be a Markov kernel from latent states to observation patterns
   and `μ` a finite measure on latent states whose singleton masses and
   singleton likelihoods are exactly the mixture weights and the locally
   independent item law. Then the responsibility `resp θ x k` is
   the real reading of the canonical posterior mass `(κ†μ) x {k}`, the
   mass described by the copied posterior singleton formula. The evidence
   `(κ ∘ₘ μ) {x}` is positive (nonzero in `ℝ≥0∞`), since the mixture
   weights and likelihoods are all positive.

The hypotheses on `κ` and `μ` are pointwise singleton identities, stated
for the fixed observation `x` in the third part; the kernel and measure
themselves are not redefined here.
