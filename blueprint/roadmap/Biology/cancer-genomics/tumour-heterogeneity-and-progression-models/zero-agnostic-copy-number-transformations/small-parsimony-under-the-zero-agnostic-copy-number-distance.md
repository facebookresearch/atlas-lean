# Small parsimony under the zero-agnostic copy number distance

**Problem.** Given a rooted tree $T$ whose $m$ leaves are labelled by copy number profiles in $\mathbb{Z}^n$, the **ZCNT small parsimony problem** asks for profiles at the internal vertices minimizing $\sum_{(u,v) \in E(T)} d(p_u, p_v)$, where $d$ is the zero-agnostic copy number distance. Through the delta map this is the problem of labelling internal vertices with delta profiles $q_u \in \mathbb{Z}^{n+1}$ satisfying the balancing condition $\sum_i (q_u)_i = 0$ so as to minimize $\sum_{(u,v)} \tfrac12 \|q_u - q_v\|_1$.

**Theorem 3.** If the balancing condition is dropped, the problem is solvable exactly in $O(mn)$ time. If integrality is dropped, it is solvable in weakly polynomial time by a linear program with $O(mn)$ variables and constraints.

**Theorem 4.** For binary trees, the ZCNT small parsimony problem can be solved to within a factor of $2$ in $O(mn)$ time.

**Median problem.** For a star tree (one internal vertex, leaves $p_1, \dots, p_m$), the median $\min_r \sum_k d(r, p_k)$ is solved exactly by a dynamic program over loci $j$ and running discrepancy $k = \sum_{i \le j} r_i$, with $A[j, k] = \min_{|b| \le B} \{A[j-1, k-b] + \sum_{k'} |b - \Delta(p_{k'})_j|\}$, $B$ the maximum input copy number, and the optimum read off at $A[n+1, 0]$ (discrepancy zero, i.e. balanced).

## Depends on

- [Closed form of the zero-agnostic copy number distance](closed-form-of-the-zero-agnostic-copy-number-distance.md)

## Expansion

Because the distance is a halved $\ell_1$ norm in delta coordinates, the objective separates over the $n+1$ coordinates; only the balancing condition couples them. Without it, each coordinate is an ordinary small parsimony problem with absolute-difference cost on a tree, solved by Sankoff/Fitch-style dynamic programming with piecewise-linear convex cost functions, in linear time. Without integrality the problem is an $\ell_1$ linear program. For the 2-approximation, any labelling agreeing with the leaves has cost at least the total discrepancy $\sum_u |\mathrm{disc}(\ell(u))|$ of its vertices (Lemma 1), and an unbalanced labelling can be rebalanced in $O(mn)$ time at extra cost at most that total discrepancy (Corollary 4), so rebalancing an optimal unbalanced labelling at most doubles the cost; the star-tree DP tracks the partial sum needed to end balanced, and restricting entries to $[-B, B]$ loses no optimality.

## Sources

- H. Schmidt, P. Sashittal, B. J. Raphael, "A zero-agnostic model for copy number evolution in cancer", PLoS Computational Biology 19 (2023) e1011590, Section 2.4, Theorems 3–4, Lemma 1, Corollary 4 and the multiple median problem, <https://doi.org/10.1371/journal.pcbi.1011590> (PMC10662746).
