# A trace-reconstruction lower bound with varying deletion probability

For a binary word of length $n$ a trace is the full ordered list of surviving bits after independent deletion with probability $q$ at each position. The positions of the surviving bits are not observed. Let $M(n,q,s)$ be the infimum, in the extended nonnegative reals, of the natural numbers $m$ for which a randomized estimator using $m$ independent traces reports each possible input word with probability at least $s$ on that input. The same estimator must work for every input; it may depend on $m,n,q$. The infimum of an empty set is $+\infty$.

Fix $0<s\le1$ and $0<c<1/(4\log 2)$. Suppose $n_k\to\infty$, $0<q_k<1$ for every $k$, and $q_k^3\log n_k\to\infty$. Then eventually

$$
M(n_k,q_k,s)\ \ge\ n_k^{\,c\log(q_k^3\log n_k)}.
$$

The product deletion-mask law gives mask $a$ mass $\prod_i [1-q\text{ if }a_i=1,\ q\text{ otherwise}]$. Push it forward along the map removing the positions whose mask values are zero, and take its $m$-fold product. An estimator is a probability vector on length-$n$ words for each tuple of received lists.

## Depends on

- [Binary deletion experiment and trace sample budgets](deletion-experiment.md)

## Expansion

Separate a growing hard input family with full trace laws close to a common reference uniformly as $q^3\log n\to\infty$ from the multiple-testing estimate for randomized decisions. Quantify its family size and product-law comparison, and show the resulting success bound for every fixed $s\in(0,1)$, including $s\le1/2$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceReconstruction.lean#L62-L73)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/122.md)
- [Accompanying manuscript: Quantitative lower bounds for trace reconstruction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf)
- [Background: Nazarov and Peres, *Trace reconstruction with exp(O(n^{1/3})) samples* (2017)](https://arxiv.org/abs/1612.03599)
