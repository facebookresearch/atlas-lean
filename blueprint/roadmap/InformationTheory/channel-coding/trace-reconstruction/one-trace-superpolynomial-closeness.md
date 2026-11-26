# Superpolynomial closeness of one-trace laws

Given fixed $0<q<1$ and distinct length-$n$ binary words $x,y$, let $P_x,P_y$ be the laws of the complete surviving lists from independent deletion of each bit with probability $q$. Set $d_n(q)=\inf_{x\ne y}\tfrac12\sum_{|w|\le n}|P_x(w)-P_y(w)|$ where $w$ runs over binary lists, including the empty list. For every fixed $C>0$, $n^Cd_n(q)\to0$ as $n\to\infty$. The infimum is a finite minimum for $n\ge1$; the real infimum of the empty set at $n=0$ is taken to be zero and does not affect the limit.

**Conventions.** Use the finite deletion-mask pushforward to complete lists and total variation, rather than one-bit or position-revealing statistics.

## Depends on

- [Binary deletion experiment and trace sample budgets](deletion-experiment.md)

## Expansion

Construct the hard word pairs at fixed deletion probability with arbitrarily high polynomial closeness. Record the full random trace distribution of those pairs and prove the quantitative total-variation estimate on the whole trace alphabet before deriving each asymptotic exponent.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceReconstruction.lean#L74-L78)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/122.md)
- [Accompanying manuscript: Quantitative lower bounds for trace reconstruction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf)
- [Background: Nazarov and Peres, *Trace reconstruction with exp(O(n^{1/3})) samples* (2017)](https://arxiv.org/abs/1612.03599)
