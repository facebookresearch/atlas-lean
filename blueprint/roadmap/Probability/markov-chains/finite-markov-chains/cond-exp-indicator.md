# Bridge: finite-state Markov chains satisfy the general one-step Markov property

**Bridge: finite-state Markov chains satisfy the general one-step Markov
property.** For a finite Markov chain, the conditional expectation of the
indicator of `X (n+1) ∈ B` given `ℱ n` is the kernel of `P` evaluated at
`X n`, almost surely. This is the one-step form of `v1`'s general
`IsMarkovChain.markov_prop` specialized to the matrix kernel. No measurability
hypothesis on `B` is needed: the indicator is defined for every set, and the
proof only sums over the finite state space.
