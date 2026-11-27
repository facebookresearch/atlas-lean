# Lower bound for perfect matchings from an edge partition

Let $V$ and $E$ be finite vertex and labelled edge sets, and let the endpoint maps $\mathrm{end}_1,\mathrm{end}_2:E\to V$ satisfy $\mathrm{end}_1(e)\ne\mathrm{end}_2(e)$ for every $e$. Distinct labels may have the same unordered endpoints. Assume $|V|=2m$ with $m>0$. A perfect matching is a subset of $E$ whose incident edge set at each vertex has cardinality one. Suppose the entire edge set is partitioned into $k\ge1$ indexed perfect matchings: each edge belongs to exactly one of them. Let $N(G)$ count all perfect matchings as labelled edge subsets, not just those in the partition. Then

$$
\bigl(k\exp(-8(1-1/k))\bigr)^m\le N(G).
$$

The power is a natural power; the division and comparison take place in the reals. For $k=1$ the displayed lower bound is $1$.

**Remark (elementary comparison).** For $k\ge1$, the inequality $-8\le -8(1-1/k)$ gives $\exp(-8)k\le k\exp(-8(1-1/k))$. Both sides are nonnegative, so raising them to the natural power $m$ gives the source's second inequality $(\exp(-8)k)^m\le\bigl(k\exp(-8(1-1/k))\bigr)^m$. Thus the former is a coarser lower bound on the count. The comparison itself does not use the graph bound.

## Depends on

- [Edges incident to a vertex](../../graph-families-and-operations/finite-multigraphs/incident.md)

## Proof depends on

- [Exponential deficit bound for perfect-matching entropy](perfect-matching-entropy-exponential-deficit.md)

## Proof outline

The uniform law on the partition supplies a feasible marginal vector $x$, with $x_e=1/k$ on every labelled edge. Each perfect matching contains $m$ edges, so the partition gives $km$ labels and the marginal entropy is $F(x)=m\log k$. For **every** matching law $p$ with these marginals, concavity of $-t\log t$ (with zero contribution at $t=0$) gives $-\sum_M p_M\log p_M\le\log N(G)$ by averaging over the $N(G)>0$ possible matchings. Taking the supremum gives $H(x)\le\log N(G)$, not just a bound for the partition law. Apply the coefficient-eight deficit estimate at $x$ to get $\log N(G)\ge m(\log k-8(1-1/k))$, and exponentiate.

## Sources

- [Count and comparison statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/Main.lean#L163-L170), [uniform decomposition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/Main.lean#L133-L160), and [bound on maximum feasible-law entropy](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/Entropy.lean#L158-L164).
- [Matching and labelled-edge conventions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingEntropy.lean#L15-L45).
- [Related manuscript theorem for selected edge-disjoint matchings](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/build/sections/04-consequences.tex#L90-L129). That statement uses a different entropy bound and permits additional edges.
