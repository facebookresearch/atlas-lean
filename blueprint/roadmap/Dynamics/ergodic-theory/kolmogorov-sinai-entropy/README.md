# Kolmogorov–Sinai entropy

Sinai's entropy of a measure-preserving transformation measures the rate at which the dynamics produces
information. A finite partition $\xi$ turns every orbit into a stationary sequence of symbols; the entropy of $T$
relative to $\xi$ is the Shannon entropy per symbol of that sequence, and the Kolmogorov–Sinai entropy $h_\mu(T)$
is its supremum over all finite partitions. It is an invariant of measure-theoretic isomorphism, it is computed by
the generator theorem, and it gives $-\sum_i p_i \log p_i$ for the Bernoulli shift with probability vector $p$,
which is how Kolmogorov and Sinai proved that the Bernoulli schemes $(\tfrac13, \tfrac13, \tfrac13)$ and
$(\tfrac12, \tfrac12)$ are not isomorphic.

- [Measurable partition modulo null sets](is-measurable-partition.md)
- [Entropy of a finite partition](partition-entropy.md)
- [Entropy of a partition is nonnegative](partition-entropy-nonneg.md)
- [Dynamical refinement of a partition](iterate-join.md)
- [Atoms of the dynamical refinement are measurable](measurable-set-iterate-join.md)
- [Entropy of a transformation relative to a partition](entropy-rel.md)
- [Kolmogorov–Sinai entropy](ks-entropy.md)
- [Relative entropy is bounded by the Kolmogorov–Sinai entropy](entropy-rel-le-ks-entropy.md)
- [Pullback of a measurable partition](preimage.md)
- [Dynamical refinement commutes with pullback along a factor map](iterate-join-preimage.md)
- [Relative entropy of a pulled-back partition](entropy-rel-preimage.md)
- [Entropy does not increase under factors](ks-entropy-le-of-factor.md)
- [Entropy is invariant under conjugacy by a measure-preserving measurable equivalence](ks-entropy-eq-of-isomorphic.md)
- [Isomorphism modulo null sets](is-isomorphic-mod0.md)
- [A conjugacy by a measure-preserving measurable equivalence is an isomorphism modulo null sets](is-isomorphic-mod0-of-measurable-equiv.md)
- [Almost-everywhere semiconjugacy passes to iterates](iterate-comp-ae-eq.md)
- [Dynamical refinement commutes with pullback, almost everywhere](iterate-join-preimage-ae-eq.md)
- [Relative entropy of a pulled-back partition under an a.e. factor map](entropy-rel-preimage-of-ae.md)
- [Entropy does not increase under factors (almost-everywhere form)](ks-entropy-le-of-factor-ae.md)
- [Entropy is an invariant of isomorphism modulo null sets](ks-entropy-eq-of-is-isomorphic-mod0.md)
- [Refinements under the identity](partition-entropy-iterate-join-id.md)
- [The identity has zero entropy](ks-entropy-id.md)
- [Sinai's generator theorem](ks-entropy-eq-entropy-rel-of-is-generato.md)
- [Sinai's generator theorem, noninvertible case](ks-entropy-eq-entropy-rel-of-is-strong-g.md)
- [Entropy of a product distribution on words](sum-neg-mul-log-prod.md)
- [Time-zero partition of the shift space](time-zero-partition.md)
- [The time-zero partition is a measurable partition](is-measurable-partition-time-zero.md)
- [Refinements of the time-zero partition are cylinders](iterate-join-time-zero.md)
- [Measure of a cylinder under a product measure](infinite-pi-cylinder-word.md)
- [Entropy of the refined time-zero partition](partition-entropy-iterate-join-time-zero.md)
- [Entropy of the Bernoulli shift relative to the time-zero partition](entropy-rel-time-zero.md)
- [Lower bound for the entropy of a Bernoulli shift](of-real-le-ks-entropy-shift.md)
- [Entropy of a Bernoulli shift](ks-entropy-bernoulli-shift.md)
- [Kolmogorov's non-isomorphism of Bernoulli schemes](not-isomorphic-bernoulli-uniform-three-t.md)
- [Ornstein's isomorphism theorem](ornstein-isomorphism.md)
- [The irrational rotation has entropy zero](ks-entropy-add-circle-rotation-eq-zero.md)

## Related topics

- [Shannon entropy and Kullback–Leibler divergence](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/README.md):
  the entropy of a partition is the Shannon entropy of the law of its atoms, and $h_\mu(T, \xi)$ is the
  entropy rate of the symbolic process it defines.
- [Entropy, dimension and Lyapunov exponents](../../smooth-dynamics/entropy-dimension-and-lyapunov-exponents/README.md):
  the formulas of Pesin, Young, Margulis and Ruelle relate Kolmogorov–Sinai entropy to Lyapunov exponents
  for smooth systems.
- [Mixing](../mixing/README.md): Bernoulli shifts are mixing, and entropy is the invariant that
  distinguishes them.
- [Full shift and cellular automata](../../topological-symbolic-dynamics/full-shift-and-cellular-automata/README.md):
  the full shift is the topological space underlying Bernoulli schemes.
