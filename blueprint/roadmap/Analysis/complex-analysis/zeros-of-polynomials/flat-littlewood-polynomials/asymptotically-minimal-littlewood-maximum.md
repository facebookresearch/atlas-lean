# Asymptotically minimal maxima of real Littlewood polynomials

For every $\eta>0$ there is an integer $N_0\geq1$ such that for every integer $N\geq N_0$ there are signs $\varepsilon_0,\ldots,\varepsilon_{N-1}\in\{-1,1\}$ with $|\sum_{k=0}^{N-1}\varepsilon_k z^k|\leq(1+\eta)\sqrt{N}$ at every complex $z$ with $|z|=1$. This is a uniform **upper** bound; it gives no pointwise lower bound near $\sqrt{N}$.

## Depends on

- [Littlewood polynomials](is-littlewood-polynomial.md), here parametrized by length $N$, not degree $N-1$.

## Proof depends on

A sign construction attaining the near-Parseval upper bound at every sufficiently large length. Flatness bounded between two fixed multiples of the square root does not imply the required upper bound.

## Expansion

Separate the construction achieving the sharp asymptotic upper bound from the length-completion estimates. Keep the full circle and all sufficiently large integer lengths; a construction along selected lengths is not enough.

## Consequences
This refutes the conjecture that some absolute $c>0$ forces every degree-$(N-1)$ Littlewood polynomial to have maximum at least $(1+c)\sqrt{N}$ on the circle: apply the theorem with $0<\varepsilon<c$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AsymptoticallyMinimalLittlewood.lean#L18-L20) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/076.md).
