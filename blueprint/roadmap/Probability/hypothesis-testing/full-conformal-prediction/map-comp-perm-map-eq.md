# Equivariant scores of exchangeable data are exchangeable

Let the law $\mu$ of the data vector $(Z_1, \dots, Z_{n+1})$ be invariant under every coordinate
permutation, and let the score map $S$ be measurable and permutation equivariant. Then the law of
the score vector $S(Z)$ is invariant under every coordinate permutation. Indeed,
$S(Z) \circ \sigma = S(Z \circ \sigma)$, and $Z \circ \sigma$ has the same law as $Z$.

This is the step that lets the split conformal bounds, which are statements about an exchangeable
score vector, apply to full conformal prediction.

## Background

- [Permutation-equivariant score map](is-perm-equivariant.md): the hypothesis on $S$.
- [Product measures are exchangeable](../../distributions/discrete/negative-binomial-and-beta-binomial-distribution/sample-rank-law/map-comp-perm-pi.md): i.i.d. data satisfy the hypothesis on $\mu$.
