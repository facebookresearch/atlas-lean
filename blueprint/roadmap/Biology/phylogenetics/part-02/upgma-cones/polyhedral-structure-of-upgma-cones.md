# Polyhedral structure of UPGMA cones

Let $d \in \mathbb{R}_{\ge 0}^{\binom{n}{2}}$ be a dissimilarity map on $[n] = \{1,\dots,n\}$. UPGMA starts from the partition $\pi_n = 1|2|\cdots|n$ and, for $i = n-1,\dots,1$, merges the two blocks $\lambda,\lambda'$ of $\pi_{i+1}$ that minimize the average linkage

$$
\bar d(\lambda,\lambda') = \frac{1}{|\lambda|\,|\lambda'|} \sum_{x \in \lambda,\ y \in \lambda'} d(x,y),
$$

which is what its weighted update of cluster distances computes. The output is a maximal chain $C = \pi_n \lessdot \pi_{n-1} \lessdot \cdots \lessdot \pi_1$ in the partition lattice $\Pi_n$, equivalently a rooted binary tree with a ranking of its internal nodes. Let $\mathcal{P}(C)$ be the closure of the set of $d$ for which UPGMA returns $C$ (the **UPGMA cone** of $C$), and $\mathcal{P}(T) = \bigcup \mathcal{P}(C)$ over the chains whose underlying tree is $T$ (the **UPGMA region** of $T$).

1. For each maximal chain $C$, $\mathcal{P}(C)$ is a pointed polyhedral cone, cut out by $d \ge 0$ and, for each step $i$, the linear inequalities $\bar d(\lambda_j^{i+1},\lambda_k^{i+1}) \le \bar d(\lambda,\lambda')$ for the merged pair $\lambda_j^{i+1},\lambda_k^{i+1}$ and every other pair of blocks of $\pi_{i+1}$ (Proposition 3.2); it has $O(n^3)$ facet-defining inequalities (Proposition 3.3) and exponentially many extreme rays (Theorem 3.1, Proposition 3.11).
2. A **traversal** of a partition $\pi_s = \lambda_1|\cdots|\lambda_s$ is a set $F$ of $\binom{s}{2}$ pairs containing exactly one pair $\{x,y\}$ with $x \in \lambda_a$, $y \in \lambda_b$ for each pair of blocks $a \ne b$; its induced vector $v(F)$ has entry $|\lambda_a|\,|\lambda_b|$ at each such pair and $0$ elsewhere. For a maximal chain $C$, the extreme rays of $\mathcal{P}(C)$ are the vectors $v(F)$ for traversals $F$ of the partitions $\pi_s$ in $C$ (Theorem 3.6, stated more generally for partial chains starting at $\pi_n$). Hence the number of extreme rays is

$$
\sum_{s=2}^{n} \prod_{a=1}^{s} |\lambda_a^{s}|^{\,s-1}.
$$

3. UPGMA regions $\mathcal{P}(T)$ are not convex in general (Corollary 4.1), the UPGMA cones do not form a fan in $\mathbb{R}^{\binom{n}{2}}$ (Corollary 4.2), and for each $n$ the comb (caterpillar) topology minimizes the number of extreme rays over all UPGMA cones (Corollary 4.3).

## Depends on

- [Average linkage between clusters](../../splits-compatibility-ultrametrics-and-upgma/avg-dist.md)

## Expansion

Each step of UPGMA compares averages of the original dissimilarities, so the condition that a given pair is merged at step $i$ is linear in $d$, and the set of inputs returning a chain is a polyhedral cone. The extreme-ray description is proved by induction along the chain, projecting the cone for the first merge onto the cone of the remaining chain through a coordinate substitution (Proposition 3.8, Lemma 3.10). Since a tree topology is the union of the cones of all its rankings, two inputs returning the same topology under different rankings can have a convex combination returning a different topology, which gives non-convexity The failure of the fan property is shown by an explicit pair of maximal chains in $\Pi_4$ whose cones meet in a set that is not a common face. The paper also estimates by Monte Carlo the spherical volumes of the regions for $n \le 7$, finding that highly unbalanced trees have small UPGMA regions.

## Sources

- Ruth Davidson, Seth Sullivant, Polyhedral combinatorics of UPGMA cones, arXiv:1206.1621 (2012). <https://doi.org/10.48550/arXiv.1206.1621>. Published version: Advances in Applied Mathematics 50(2) (2013), 327–338, <https://doi.org/10.1016/j.aam.2012.10.002>; locators above refer to the arXiv version.
