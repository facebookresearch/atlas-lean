# Exponential deficit bound for perfect-matching entropy

Let a finite loopless multigraph with labelled edges have $2m$ vertices, $m>0$, and a perfect matching. A perfect matching is an edge subset with exactly one incident edge at every vertex; each edge label gives a separate indicator coordinate. Let $y$ lie in the convex hull of these indicator vectors. Put $F(y)=-\sum_e y_e\log y_e$ with $0\log0=0$. Let $H(y)$ be the supremum of $-\sum_M p_M\log p_M$ over nonnegative weights $p_M$ of total one on perfect matchings satisfying $\sum_{M\ni e}p_M=y_e$ for every $e$. Then $F(y)-H(y)\le8m(1-\exp(-F(y)/m))$.

## Depends on

- [Edges incident to a vertex in an endpoint-map multigraph](../../graph-families-and-operations/finite-multigraphs/incident.md), with the two endpoints of each edge required to differ.

## Expansion

- Separate the existence of an entropy-maximizing law at each feasible marginal from lower semicontinuity of $H$ on the whole labelled matching polytope. The first follows from the nonempty compact feasible-law fiber; the second must handle boundary marginals as well. Once these facts are available, the barrier deficit $D(x)=F(x)-H(x)-8m(1-\exp(-F(x)/m))$ attains its maximum by compactness and upper semicontinuity.
- Separate the normalized indicator covariance facts, which do not assume that $x$ maximizes $D$. Put $s=|\{e:x_e>0\}|$. On those positive coordinates, center each indicator at $x_e$ and divide by $\sqrt{x_e}$. The resulting covariance $C$ is positive semidefinite and has trace $s-m$ for any law with marginals $x$. For an entropy-maximizing law with these marginals, use the tangent directions of the minimal face and the face codimension bound to obtain rank at least $s-4m$.

## Proof outline

If the maximum deficit is positive, fix a maximizer $x$ and an entropy-maximizing law with those marginals. For the exponential barrier, prove the second variation at $x$: every real direction $u$ on the positive coordinates satisfies $(8\exp(-F(x)/m)-1)\lVert Cu\rVert_2^2+u^{\mathsf T}Cu\le0$. The small-entropy inequality for the barrier gives $F(x)/m>\log 8$. The support entropy bound $F(x)/m\le\log(s/m)$ then gives $s>8m$ and $8m/s\le8\exp(-F(x)/m)$. Use the second variation to bound every positive covariance eigenvalue from below and contradict the trace and rank bounds. Only positive marginal coordinates are normalized; zero marginals do not require division.

## Sources

- [Comparator statement: `OAI.MatchingEntropy.entropy_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingEntropy.lean#L57-L64)
- [Attainment for feasible laws](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/Entropy.lean#L141-L149) and [boundary lower semicontinuity and attainment of the deficit maximum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/Continuity.lean#L37-L77).
- [Entropy deficit proof](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/Main.lean#L85-L130), [covariance rank](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L106-L132), and [trace and second variation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L186-L213).
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/113.md)
