# Spectral gap and mixing time for the lazy graph switch chain

Let $n\ge4$ and let $d:[n]\to\{0,\ldots,n-1\}$ be graphical. Write $N=|\mathcal G_d|$. On the labelled realizations, stay put with probability $1/2$; otherwise choose uniformly a four-set and one of the six ordered pairs of distinct perfect matchings on it. Replace the first matching by the second if valid, and stay put if not. Let $P$ be this transition matrix and $u$ the uniform law on the $N$ states. Set $t_{\rm mix}=\min\{t\in\mathbb N:\ \|P^t(G,\cdot)-u\|_{\rm TV}\le1/4\text{ for all }G\}$.

The time exists and is at most $2n^8$. If $N=1$, mixing already holds at $t=0$ and the minimum is zero. If $N>1$, for every real test function $f$ on the state space,

$$
\frac{\operatorname{Var}_u(f)}{24n^2\binom n4}\;\le\;\langle f,(I-P)f\rangle_u,
$$

where the inner product is the uniform average of the product.

**Conventions.** The transition places mass $1/(12\binom n4)$ on each ordered proposal, including failed proposals in the diagonal mass. Total variation is half the sum of absolute atom differences.

## Depends on

- [The lazy switch chain on labelled degree realizations](degree-sequence-switch-kernel.md)

## Proof outline

A degree-sequence-uniform Poincaré bound for this proposal kernel and the uniform-stationary reversible-chain estimate from spectral gap to total variation.

Build the native finite-state kernel with a one-to-one correspondence between its successful moves and the source proposals. Prove its uniform stationarity by reversing the ordered pair. Separate the Poincaré estimate, the spectral-to-mixing deduction, and the one-state case. The gap is not postulated and the assertion is not an exact sampler.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SwitchChain.lean#L155-L158)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/131.md)
- [Accompanying manuscript: Polynomial mixing of the switch chain for every graphical degree sequence](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf)
- [Background: Cooper, Dyer and Greenhill, *Sampling regular graphs and a peer-to-peer network*, Combinatorics, Probability and Computing 16 (2007), 557–593](https://doi.org/10.1017/S0963548306007978)
