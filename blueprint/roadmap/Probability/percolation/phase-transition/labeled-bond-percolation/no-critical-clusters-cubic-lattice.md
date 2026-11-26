# No infinite critical bond or site cluster on the cubic lattice

On $\mathbb Z^3$, each unoriented nearest-neighbor edge is indexed once by $(x,i)$ for the step from $x$ to $x+e_i$. In bond percolation these edges are independently open with probability $p$ and the cluster at $x$ is the set reachable by finite open paths, including $x$. In site percolation the vertices are independently open with probability $p$ and two nearest neighbors are linked only when both are open; the cluster at a closed vertex is empty. For a model, its critical probability is the infimum over $p\in[0,1]$ with positive probability of an infinite origin cluster. Each model uses its own threshold.

At the bond threshold, almost surely every bond cluster is finite. At the site threshold, almost surely every site cluster is finite. The two laws need not be coupled.

**Conventions.** Use the nearest-neighbor lattice and the two product Bernoulli laws. A real parameter passed to either Bernoulli law is clamped to $[0,1]$.

## Depends on

- [Cubic bond and site percolation and their origin thresholds](cubic-bond-and-site-laws.md)

## Proof depends on

- [Absence of infinite critical clusters on quasi-transitive bond graphs](no-critical-infinite-cluster.md)

## Expansion

For the bond half, send the label $(x,i)$ to the unordered pair $\{x,x+e_i\}$ and identify a Boolean configuration with its set of true labels. Match the independent bond laws at every $p\in[0,1]$ and the finite-path clusters, including the zero-length path. Coordinate paths give connectivity, exactly six bonds are incident to each vertex, and simultaneous translations of the vertex and bond labels preserve incidence and act transitively on vertices. Show that infinite-cluster events are measurable; by translation invariance of the product law and countability, positive probability at the origin is equivalent to positive probability that some infinite cluster exists; hence the two bond thresholds agree. Prove the threshold is below one, for example via supercritical bond percolation in a coordinate plane, before applying the linked result.

For the site half, isolate the critical-origin exclusion for the independent site law at its own threshold, or supply a reduction that preserves that law, threshold and infinite-cluster events. Then translate the null event to every vertex and take a countable union. Simply declaring an edge open when both endpoints are open does not give independent bonds: for two edges sharing one endpoint the joint opening probability is $p^3$, not $p^4$ for $0<p<1$. Keep the cluster at a closed vertex empty.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalZ3.lean#L56-L60)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/213.md)
- [Accompanying manuscript: Critical bond and site percolation on the cubic lattice](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Critical-bond-and-site-percolation-on-the-cubic-lattice-September-24-2026/paper.pdf)
