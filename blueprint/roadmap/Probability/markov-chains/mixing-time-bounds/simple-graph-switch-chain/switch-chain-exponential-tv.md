# An exponential total-variation bound for the graph switch chain

For $n\ge4$ and a graphical degree function $d:[n]\to\{0,\ldots,n-1\}$ with $N>1$ labelled simple undirected realizations, use the lazy switch chain and its uniform law $u$ defined in the [lazy switch-chain model](degree-sequence-switch-kernel.md). The total-variation distance is half the sum of absolute differences in mass. For every $t\in\mathbb N$ and starting realization $G$,

$$
\|P^t(G,\cdot)-u\|_{\rm TV}\le\frac{\sqrt N}{2}\exp\!\left(-\frac{t}{24n^2\binom n4}\right).
$$

## Depends on

- [The lazy switch chain on labelled degree realizations](degree-sequence-switch-kernel.md)

## Proof depends on

- [The switch-chain gap estimate](switch-chain-gap-and-mixing.md)

## Proof outline

Apply lazy reversible $L^2$ contraction to the density of the point mass at $G$ relative to the uniform law and then pass from the $L^2$ norm to total variation by Cauchy–Schwarz. Retain the normalization $\sqrt N/2$ and integer $t$, including $t=0$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SwitchChain.lean#L159-L162)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/131.md)
- [Accompanying manuscript: Polynomial mixing of the switch chain for every graphical degree sequence](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf)
- [Background: Cooper, Dyer and Greenhill, *Sampling regular graphs and a peer-to-peer network*, Combinatorics, Probability and Computing 16 (2007), 557–593](https://doi.org/10.1017/S0963548306007978)
