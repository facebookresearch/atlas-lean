# ALLDIFFERENT has no polynomial-size CNF decomposition

The domain consistency propagators of ALLDIFFERENT on $m$ variables with common initial domain $\{1,\dots,m\}$ have no CNF decompositions of size polynomial in $m$ on which unit propagation simulates them; the obstruction is unconditional and comes from Razborov's superpolynomial monotone circuit lower bound for bipartite perfect matching.

For $m\ge1$ let $\mathcal A_m$ be the constraint $\mathrm{ALLDIFFERENT}(X_1,\dots,X_m)$ with every initial domain equal to $\{1,\dots,m\}$, so that the direct encoding has $|\mathbf x|=m^2$ literals $x_{i,j}$ and the current domains range over all subdomains.

**Theorem.** There is no polynomial $p$ such that, for every $m$, the domain consistency propagator of $\mathcal A_m$ has a [CNF decomposition](../cnf-decomposition-of-a-propagator.md) of size at most $p(m)$. The same holds for the [global cardinality constraint](global-cardinality-constraint.md) on the same variables and values with all quotas $[0,1]$, which is the same constraint, and for any constraint type whose instances include these.

## Depends on

- [CNF decompositions of propagators and consistency checkers](../cnf-decomposition-of-a-propagator.md): the decompositions ruled out.
- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): the constraint.
- [Global cardinality constraint and its value network](global-cardinality-constraint.md): the cardinality-constraint form of the statement.

## Proof depends on

- [Polynomial CNF decompositions are polynomial monotone circuits](../cnf-decompositions-and-monotone-circuits.md): polynomial-size decompositions of the domain consistency propagators give polynomial-size monotone circuits for the induced checkers.
- [Generalized arc consistency of ALLDIFFERENT by matchings](alldifferent-gac-matching-criterion.md): the constraint has a solution iff its value graph has a matching covering the variables.
- [Monotone circuits for bipartite perfect matching need superpolynomial size](../monotone-circuit-lower-bound-for-perfect-matching.md): Razborov's $m^{\Omega(\log m)}$ bound for the logical permanent $f_m$.

## Expansion

The checker induced by the domain consistency propagator of $\mathcal A_m$ outputs 1 on a subdomain exactly when $\mathcal A_m$ has a solution in it. Reading the subdomain as its characteristic vector $(b_{i,j})_{i,j\le m}$, $b_{i,j}=1$ iff $j$ is still in $D(X_i)$, the value graph is the subgraph $E=\{(i,j):b_{i,j}=1\}$ of $K_{m,m}$, and with $m$ values a matching covering the variables is a perfect matching. So the checker is exactly the perfect matching function $f_m$ of the $m^2$ edge bits. A family of decompositions of size $p(m)$ would give monotone flat circuits with a number of gates polynomial in $m$ for $f_m$, contradicting the $m^{\Omega(\log m)}$ lower bound, which holds for circuits of any fan-in (the fan-in-two bound and the $g^2$ conversion recorded on the lower-bound page). With all quotas $[0,1]$ the global cardinality constraint allows exactly the same tuples.

The bound needs no complexity-theoretic assumption, in contrast with obstructions derived from NP-hardness of propagation; enforcing GAC on ALLDIFFERENT itself takes polynomial time.

By contrast, bounds and range consistency propagators of ALLDIFFERENT do have polynomial-size decompositions (Hall-interval decompositions), propagated by local consistency on Boolean reifications and sums rather than by unit propagation on clauses.

## Sources

- C. Bessiere, G. Katsirelos, N. Narodytska and T. Walsh, "Circuit complexity and decompositions of global constraints", *Proceedings of the Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 2009)*, 412–417, [https://www.ijcai.org/proceedings/2009/76](https://www.ijcai.org/proceedings/2009/76). Corollary 4 and its proof, and the extension to generalizations of ALLDIFFERENT such as the global cardinality constraint stated before it, §5 of arXiv:0905.3757v1, [https://arxiv.org/abs/0905.3757v1](https://arxiv.org/abs/0905.3757v1).
- S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Algorithms and Combinatorics 27, Springer (2012), doi:10.1007/978-3-642-24508-4. §9.11, the perfect matching function $f_m$ on the $m^2$ edge variables of $K_{m,m}$ and Theorem 9.38; author copy [https://web.vu.lt/mif/s.jukna/boolean/Chapter9.pdf](https://web.vu.lt/mif/s.jukna/boolean/Chapter9.pdf).
