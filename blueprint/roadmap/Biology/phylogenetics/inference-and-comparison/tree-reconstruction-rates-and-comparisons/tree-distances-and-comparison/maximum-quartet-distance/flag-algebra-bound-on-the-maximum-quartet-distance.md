# Flag-algebra bound on the maximum quartet distance

A **quartet** $[ab|cd]$ on four taxa is the unrooted binary tree separating $\{a,b\}$ from $\{c,d\}$; a phylogenetic tree $T$ on a taxon set $\mathcal X$ **displays** $[ab|cd]$ if the paths from $a$ to $b$ and from $c$ to $d$ in $T$ are disjoint. For two phylogenetic trees $T_1, T_2$ on the same $n$ taxa, the **quartet distance** $\mathrm{qd}(T_1,T_2)$ is $\binom n4$ minus the number of quartets displayed by both trees, i.e. the number of four-taxon subsets on which they induce different topologies. A **caterpillar** is a tree whose internal vertices lie on one path.

**Facts.** If $T$ is a tree and its leaves are labelled by a uniformly random bijection onto $\mathcal X$, it displays on average one third of any fixed set of quartets; consequently two independent uniform random trees have $\mathbb E[\mathrm{qd}(T_1,T_2)] = \tfrac23\binom n4$. Bandelt and Dress conjectured that the maximum is asymptotically the same, $\max \mathrm{qd} = (\tfrac23 + o(1))\binom n4$.

**Theorem.** For all phylogenetic trees $T_1, T_2$ on $n$ leaves,

$$\mathrm{qd}(T_1,T_2) \le (0.69 + o(1))\binom n4.$$

**Theorem (caterpillars).** For phylogenetic caterpillar trees $T_1, T_2$ on $n$ leaves,

$$\mathrm{qd}(T_1,T_2) \le \Big(\frac23 + o(1)\Big)\binom n4,$$

so the Bandelt–Dress conjecture holds for caterpillars.

## Expansion

View the pair $(T_1,T_2)$ as a single combinatorial structure (a tree-pair) and count, among its $4$-leaf sub-structures, the induced copies of the configuration $cr_4$ in which the two trees disagree; the quartet distance is exactly this count. Flag algebras express densities of small sub-configurations as polynomial identities via the chain rule, $p_\sigma(F_1,\dots,F_m;F) = \prod_i p_\sigma(F_i;F) + O(1/n)$ for products of flags, and Cauchy–Schwarz-type inequalities become a semidefinite program over all tree-pairs of a fixed small order. Solving that program numerically and rounding to an exact certificate (controlled by elementary matrix-norm bounds) gives the density bound $0.69$. For caterpillars, each tree is encoded by a linear order of its leaves, and the same method on pairs of orders reaches the conjectured constant $2/3$.

## Sources

- Noga Alon, Humberto Naves, Benny Sudakov, "On the maximum quartet distance between phylogenetic trees", arXiv (2015). Section 1 (Conjecture 1.1, Theorems 1.2 and 1.3), Section 2 (Propositions 2.1–2.3), Section 3 (Theorem 3.1, Propositions 3.2–3.3), Section 4 (Proposition 4.1). <https://doi.org/10.48550/arXiv.1505.04344>. Published version: SIAM Journal on Discrete Mathematics 30(2) (2016), 718–735, <https://doi.org/10.1137/15m1041754>; locators above refer to the arXiv version.
