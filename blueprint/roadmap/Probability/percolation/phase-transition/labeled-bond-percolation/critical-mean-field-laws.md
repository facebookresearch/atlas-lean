# Mean-field tails and two-point decay on nonamenable bond graphs

Under the infinite, connected, locally finite, quasi-transitive and positive vertex-expansion assumptions of the [operator-threshold theorem](operator-threshold-and-simultaneous-nonuniqueness.md), the following hold.

* At each vertex $x$ the critical sum $\sum_{a,b}\tau_{p_c}(x,a)\tau_{p_c}(a,b)\tau_{p_c}(b,x)$ is finite and at most $N(p_c)^3$.
* For each $x$, $\chi_p(x)=\sum_y\tau_p(x,y)$ is between positive constant multiples of $(p_c-p)^{-1}$ for $p<p_c$ sufficiently close to $p_c$. The probability that $x$ is in an infinite cluster is between positive constant multiples of $p-p_c$ for $p>p_c$ sufficiently close to $p_c$.
* At $p_c$ the probabilities that the cluster at $x$ has at least $n$ vertices, contains a vertex at intrinsic distance at least $n$, and contains a vertex at ambient graph distance at least $n$ are bounded above and below by positive multiples of $n^{-1/2},n^{-1},n^{-1}$ respectively, for all integers $n\ge1$. Constants may depend on $x$ and on the event. Intrinsic distance uses the open graph, ambient distance the full graph.
* Let $p_{\exp}$ be the supremum of the $p$ admitting $\tau_p(x,y)\le A e^{-a d_G(x,y)}$ for some $A,a>0$ uniformly in $x,y$. Then $p_c<p_2\le p_{\exp}$, and the exponential bound holds for each $p<p_2$.

**Conventions.** Use extended sums for the triangle diagram and ordinary real sums for the stated subcritical susceptibility.

## Depends on

- [Independent bonds with separate edge labels](labelled-independent-bond-law.md)
- [The percolation thresholds and operator norm](operator-threshold-and-simultaneous-nonuniqueness.md)

## Proof depends on

Critical $\ell^2$ boundedness, the diagram inequalities underlying the susceptibility and density estimates, and the critical intrinsic/extrinsic one-arm estimates. Decay needs the operator-threshold argument below $p_2$.

## Expansion

Separate the triangle bound, the two near-critical laws, each of the three critical tails and the sub-operator-threshold exponential bound. The triangle condition by itself must not be marked as already yielding the entire list, especially the ambient distance tail.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BenjaminiSchramm.lean#L222-L227)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/214.md)
- [Accompanying manuscript: Nonuniqueness of percolation on nonamenable quasi-transitive graphs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf)
