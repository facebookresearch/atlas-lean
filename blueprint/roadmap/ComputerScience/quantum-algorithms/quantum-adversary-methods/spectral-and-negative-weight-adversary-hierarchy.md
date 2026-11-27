# Spectral and negative-weight adversaries and their hierarchy

For a partial Boolean function $f$ on $D \subseteq \{0,1\}^N$, the *spectral adversary* is $\mathrm{ADV}(f) = \max_\Gamma \|\Gamma\| / \max_i \|\Gamma \circ D_i\|$ over nonzero symmetric entrywise nonnegative matrices $\Gamma$ indexed by $D$ vanishing on pairs with $f(x) = f(y)$, and the *negative-weight adversary* $\mathrm{ADV}^\pm(f)$ is the same maximum over all real symmetric such $\Gamma$. Then, for every $0 \le \varepsilon < 1/2$:

$$\lambda(f) \le \mathrm{ADV}(f) \le \mathrm{ADV}^\pm(f), \qquad \big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\mathrm{ADV}^\pm(f) \le 2 Q_\varepsilon(f)$$

(for a function with a finite output set of more than two values the constant is $1 - 2\sqrt{\varepsilon(1-\varepsilon)} - 2\varepsilon$); Zhang's strong weighted bound equals $\mathrm{ADV}(f)$; and the *property testing barrier* holds: if every pair of inputs with different values is at Hamming distance at least $k \ge 1$ then $\mathrm{ADV}(f) \le N/k$.

## Proof sketch

The lower bounds on $Q$ follow the progress method with the principal eigenvector of $\Gamma$ as weights. For spectral sensitivity take $\Gamma$ the adjacency matrix of the sensitivity graph: $\|\Gamma\| = \lambda(f)$ and each $\Gamma \circ D_i$ is a matching, of norm at most $1$. Weight schemes and nonnegative adversary matrices are converted into each other with the principal eigenvector and a Schur-product argument. For the barrier, $\sum_i \Gamma \circ D_i \ge k\,\Gamma$ entrywise for nonnegative $\Gamma$, so by monotonicity of the norm on nonnegative matrices and the triangle inequality some $i$ has $\|\Gamma \circ D_i\| \ge k\|\Gamma\|/N$.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)
- [Generalized adversary lower bound](../quantum-query-lower-bounds/generalized-adversary-lower-bound.md)
- [Sensitivity graph and spectral sensitivity](../../../TheoryOfComputation/communication-complexity/sensitivity-certificates-and-degree/spectral-sensitivity.md)
- [Weighted adversary bounds (Ambainis, Zhang)](weighted-quantum-adversary-bounds.md)

## Sources

- H. Barnum, M. Saks and M. Szegedy, "Quantum Query Complexity and Semi-Definite Programming", 18th IEEE Conference on Computational Complexity (CCC 2003), 2003: the spectral adversary bound.
- R. Špalek and M. Szegedy, "All Quantum Adversary Methods Are Equivalent", Theory of Computing 2, 2006, Theorem 3.1 and Section 4: spectral equals strong weighted adversary.
- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", STOC 2021, Lemma 9: $\lambda(f) \le \mathrm{ADV}(f)$.
- P. Høyer, T. Lee and R. Špalek, "Negative Weights Make Adversaries Stronger", STOC 2007, Theorems 1 and 2 (constants) and Section 1 (property testing barrier).
