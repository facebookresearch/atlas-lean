# Superpolynomial trace sample complexity at fixed deletion probability

For $q\in(0,1)$ and $s\in(0,1]$, let $M(n,q,s)$ be the infimum of fixed natural sample budgets for a randomized decoder that sees only the surviving lists from independent deletion traces of an unknown $n$-bit word. The success probability must be at least $s$ for every input. An insufficient channel has infimum $+\infty$ when there is no such budget. For every real $C>0$,

$$
\lim_{n\to\infty} \frac{M(n,q,s)}{n^C}=+\infty
$$

in the extended nonnegative reals, with real powers embedded into that type.

**Conventions.** Use the [deletion experiment and sample-budget definition](deletion-experiment.md).

## Depends on

- [Binary deletion experiment and trace sample budgets](deletion-experiment.md)

## Proof depends on

- [A trace-reconstruction lower bound with varying deletion probability](varying-noise-sample-lower-bound.md)

## Proof outline

Specialize the varying-noise bound to the constant $q$ and $n_k=k$, choose any admissible positive $c$, and use $c\log(q^3\log n)-C\to\infty$. No lower bound on $s$ above $1/2$ is needed.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceReconstruction.lean#L79-L86)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/122.md)
- [Accompanying manuscript: Quantitative lower bounds for trace reconstruction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf)
- [Background: Nazarov and Peres, *Trace reconstruction with exp(O(n^{1/3})) samples* (2017)](https://arxiv.org/abs/1612.03599)
