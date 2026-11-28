# Alon-Krivelevich-Sudakov: spectral recovery of a planted clique

Let $G$ be drawn from $G(n, 1/2, k)$: a random graph $G(n, 1/2)$ in which a $k$-set $Q$ of vertices is made a clique (by symmetry the choice of $Q$ does not matter). **Algorithm A** of Alon, Krivelevich and Sudakov computes a unit eigenvector $v_2$ for the second largest eigenvalue of the adjacency matrix of $G$, lets $W$ be the $k$ vertices whose coordinates in $v_2$ are largest in absolute value (ties broken arbitrarily), and outputs the set of vertices with at least $3k/4$ neighbours in $W$. If $k \ge 10\sqrt n$ and $k = O(\sqrt{n \log n})$, then almost surely, that is with probability tending to $1$ as $n \to \infty$, the second eigenvector is unique up to scaling and Algorithm A outputs exactly $Q$.

## Proof sketch

Following Alon, Krivelevich and Sudakov, Section 2.2, let $z$ have $z_v = n - k$ on $Q$ and $z_v = -k$ off $Q$. Applying the strong Bai–Yin upper bound to the symmetric $\pm 1$ matrix $2A_1 - J + I$ of $G(m, 1/2)$ (adding independent $\pm 1$ signs on the diagonal changes the operator norm by at most $1$) gives $\lambda_2(A_1) \le (1 + o(1))\sqrt m$ with probability tending to $1$ (as in AKS Lemma 2.2). By Courant–Fischer min–max on the adjacency matrix $A$, the eigenvalues satisfy $\lambda_1 \ge (1/2 + o(1))n$ and $\lambda_i \le (1 + o(1))\sqrt n$ for $i \ge 3$ almost surely (Proposition 2.1). By two-sided Hoeffding and Chebyshev bounds on the vertex degrees, $\|(A - \frac{k}{2}I)z\|_2^2 \le (\frac14 + o(1))n^3 k$ almost surely (Lemma 2.4). Combining Proposition 2.1 and Lemma 2.4 gives Proposition 2.3: almost surely some multiple of $v_2$ equals $z - d$ with $\|d\|_2^2 \le \|z\|_2^2/60 \le kn^2/60$, while Corollary 2.5 gives uniqueness of $v_2$ up to scaling. On this event (for $n$ large enough that $k < n/6$), the almost-sure degree-cleanup recovery lemma applies directly to $v_2$, showing that almost surely the degree cleanup outputs exactly $Q$.

## Depends on

- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)

## Proof depends on

- [Exact recovery of a planted clique by degree cleanup](planted-clique-deterministic-recovery.md)
- [Strong Bai–Yin theorem, upper bound](../../../Probability/high-dimensional-probability/operator-norm-of-random-matrices/wigner-op-norm-le-two-add.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)
- [Chebyshev's inequality](../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)
- [Courant–Fischer min–max, lower-bound form](../../../Analysis/operator-theory/eigenvalue-inequalities/courant-fischer-min-max-theorem/exists-unit-ge-of-submodule.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998, Section 2 (Algorithm A in Section 2.1; Proposition 2.1, Lemma 2.2, Proposition 2.3, Lemma 2.4, Corollary 2.5 and the correctness argument in Section 2.2).
