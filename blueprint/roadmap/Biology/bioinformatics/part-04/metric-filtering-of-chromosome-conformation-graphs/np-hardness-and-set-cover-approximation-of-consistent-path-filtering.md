# NP-hardness and set-cover approximation of consistent path filtering

**Problem (Consistent-$k$-Paths).** Given an integer $k \ge 2$ and a graph $G = (V,E)$ whose edges carry a nonnegative length $d(e)$ (an inferred spatial distance) and a positive reward $r(e)$ (a confidence), find $S \subseteq E$ maximizing $R(S) = \sum_{e\in S} r(e)$ such that every $e \in S$ is $k$-consistent: for every path $P$ of at most $k$ edges of $S$ joining the endpoints of $e$,

$$\sum_{e'\in P} d(e') \ \ge\ d(e). \tag{1}$$

The case $k = 2$ (only triangles must satisfy the triangle inequality) is ConsT; the case $k = |V| - 1$ (every path) is ConsP.

**Theorem.** Consistent-$k$-Paths is NP-hard for every $k \ge 2$, and remains NP-hard when all rewards are $1$.

**Approximation for ConsT.** Let $\bar\Delta$ be the set of triangles of $G$ violating the triangle inequality, and for each edge $\{u,v\}$ let $S_{uv} \subseteq \bar\Delta$ be the violated triangles containing it, with cost $r(\{u,v\})$. Removing a set of edges leaves a consistent graph iff the corresponding sets cover $\bar\Delta$, so ConsT is equivalent to minimum-weight set cover on $\{S_{uv}\}$ (maximizing the kept reward = minimizing the removed reward). Since every violated triangle lies in exactly three sets, an LP-rounding algorithm removes at most $3$ times the optimal removed reward.

## Proof depends on

- [INDEPENDENT-SET is NP-hard](../../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/ind-set-dec-np-hard.md)

## Expansion

The reduction is from Independent Set. Given $G$ and $\ell$, add a vertex $u$ joined to every vertex, give the original edges $d = r = 3$ and the new edges $d = r = 1$. Any path of three or more edges has length at least $3$ and so violates nothing; violations come only from triangles $u,v,w$ with $\{v,w\} \in E$, since $1 + 1 < 3$. Taking all original edges plus the spokes to an independent set $I$ is consistent with reward $3|E| + |I|$. Conversely, an optimal solution can be assumed to contain all original edges (swapping a spoke for a missing original edge never lowers the reward), and then the chosen spokes must end in an independent set; so reward $\ge 3|E| + \ell$ is achievable iff $G$ has an independent set of size $\ell$. With unit rewards the same swap argument works with threshold $|E| + \ell$. Applied to yeast 4C data, triangle-consistent filtering kept more total confidence than a standard 1% false-discovery filter while giving 3D embeddings with lower error and less sensitivity to initialization.

## Sources

- G. Duggal, R. Patro, E. Sefer, H. Wang, D. Filippova, S. Khuller, C. Kingsford, "Resolving spatial inconsistencies in chromosome conformation measurements", Algorithms for Molecular Biology 8:8 (2013), Problem 1 (Eq 1), Definitions 1–2, Theorem 1, Corollary 1 and the set-cover algorithm, <https://doi.org/10.1186/1748-7188-8-8>, PMCID PMC3655033.
