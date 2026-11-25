# Policy iteration is strongly polynomial for a fixed discount factor

Consider finite discounted Markov decision processes with $n$ states, $m$ state-action pairs and discount factor
$\gamma \in [0,1)$. Howard's policy iteration returns an optimal policy after at most

$$(m - n)\Big(1 + \frac{1}{1-\gamma}\log\frac{n}{1-\gamma}\Big)$$

iterations. In particular, for each fixed $\gamma$ the number of iterations is bounded by a polynomial in $n$ and $m$,
independent of the bit sizes of the rewards and transition probabilities, and policy iteration is strongly
polynomial.

Ye (2011) first proved a bound of this kind, $(m-n)\big(1 + \frac{n^2}{1-\gamma}\log\frac{n^2}{1-\gamma}\big)$, for
Howard's policy iteration and for the simplex method with Dantzig's rule; the bound displayed above is the
improvement by Hansen, Miltersen and Zwick (2013).

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: LP formulation and occupancy-measure duality.

## Proof depends on

- [Policy improvement theorem](../policy-iteration/policy-value-le-policy-value-improve.md)

## Sources

- J. Huang, *Recent progress on the complexity of solving Markov decision processes* (survey write-up, Cornell ORIE), §2.3.1, bounds (14) and (19), which cite Ye (2011) and Hansen, Miltersen and Zwick (2013). <https://people.orie.cornell.edu/jh2543/prelimWriteup.pdf>
