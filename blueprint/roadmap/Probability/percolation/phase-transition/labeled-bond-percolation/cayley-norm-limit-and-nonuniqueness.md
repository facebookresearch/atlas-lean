# Critical norm limit and nonuniqueness for prescribed Cayley generators

Let $\Lambda$ be a group failing the right Følner condition: it is not true that for every finite $K\subset\Lambda$ and $\epsilon>0$ some finite nonempty $A$ has $|(Ak)\setminus A|<\epsilon|A|$ for all $k\in K$. Take any finite symmetric generating set $S$ with $1\notin S$. Use the simple Cayley graph on vertices $\Lambda$ with edges $\{x,xs\}$, $s\in S$, each distinct unordered edge counted once.

With the [bond thresholds and operator norm](labelled-independent-bond-law.md), the two-point matrix at $p_c$ defines a bounded operator, $\sup_{p<p_c}N(p)=N(p_c)<\infty$, and $p_c<p_2\le p_u$. There is a closed interval $[a,b]$ with $p_c<a<b<1$ such that in the common uniform edge-label coupling there are infinitely many infinite clusters simultaneously at all $p\in[a,b]$, almost surely. Furthermore, for every fixed $p\in(p_c,p_u)$ the Bernoulli law at $p$ has infinitely many infinite clusters almost surely.

**Conventions.** Use the right Følner condition and right-multiplication Cayley graph, with the labelled-bond framework above restricted to distinct Cayley edges.

## Depends on

- [Independent bonds with separate edge labels](labelled-independent-bond-law.md)

## Proof depends on

- [Critical operator norms and the coupled nonuniqueness interval](operator-threshold-and-simultaneous-nonuniqueness.md)

Also use the equivalence from nonamenability to positive vertex expansion for the chosen generating set and the infinite-cluster number trichotomy in the transitive Bernoulli law.

## Expansion

Show the Cayley graph has the requisite connectivity, degree and expansion properties for every prescribed $S$. Separate the stronger from-below norm identity from the [separate Cayley corollary](cayley-operator-boundedness-and-gap.md) that asserts boundedness but not the from-below identity. Use the trichotomy to extend the fixed-parameter nonuniqueness claim to the whole open interval, without changing the separate coupled-interval claim.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BenjaminiSchramm.lean#L228-L237)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/214.md)
- [Accompanying manuscript: Nonuniqueness of percolation on nonamenable quasi-transitive graphs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf)
