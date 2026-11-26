# Spectral and negative-weight adversaries and their hierarchy

For a partial Boolean function $f$ on $D \subseteq \{0,1\}^N$, the *spectral adversary* is $\mathrm{ADV}(f) = \max_\Gamma \|\Gamma\| / \max_i \|\Gamma \circ D_i\|$ over nonzero symmetric entrywise nonnegative matrices $\Gamma$ indexed by $D$ vanishing on pairs with $f(x) = f(y)$, and the *negative-weight adversary* $\mathrm{ADV}^\pm(f)$ is the same maximum over all real symmetric such $\Gamma$. Then:

$$\lambda(f) \le \mathrm{ADV}(f) \le \mathrm{ADV}^\pm(f), \qquad \big(1 - 2\sqrt{\varepsilon(1-\varepsilon)} - \varepsilon\big)\mathrm{ADV}^\pm(f) \le 2 Q_\varepsilon(f)$$

(for Boolean outputs with constant $1 - 2\sqrt{\varepsilon(1-\varepsilon)}$), the weighted (Zhang) bound is at most $\mathrm{ADV}(f)$, and the *certificate barrier* holds: if every pair of inputs with different values is at Hamming distance at least $k$ then $\mathrm{ADV}(f) \le N/k$.

## Proof sketch

The upper bounds on $Q$ follow the progress method with the principal eigenvector of $\Gamma$ as weights. Spectral sensitivity is the case $\Gamma = A_f$ restricted to $D_i$ structure. Weighted schemes yield nonnegative $\Gamma$ by a Schur-product argument. For the barrier, $\sum_i \Gamma \circ D_i \ge k\,\Gamma$ entrywise for nonnegative $\Gamma$, so some $i$ has $\|\Gamma \circ D_i\| \ge k\|\Gamma\|/N$.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)
- [Generalized adversary lower bound](../quantum-query-lower-bounds/generalized-adversary-lower-bound.md)
- [Sensitivity graph and spectral sensitivity](../../../TheoryOfComputation/communication-complexity/sensitivity-certificates-and-degree/spectral-sensitivity.md)

## Proof depends on

- [Weighted adversary bounds (Ambainis, Zhang)](weighted-quantum-adversary-bounds.md)

## Sources

- H. Barnum, M. Saks and M. Szegedy, "Quantum Query Complexity and Semi-Definite Programming", IEEE Conference on Computational Complexity, 2003.
- P. Høyer, T. Lee and R. Špalek, "Negative Weights Make Adversaries Stronger", STOC 2007.
