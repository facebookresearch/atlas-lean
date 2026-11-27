# Alon-Krivelevich-Sudakov: spectral recovery of a planted clique

Let $G$ be drawn from $G(n, 1/2, k)$: a random graph $G(n, 1/2)$ in which a $k$-set $Q$ of vertices is made a clique (by symmetry the choice of $Q$ does not matter). **Algorithm A** of Alon, Krivelevich and Sudakov computes a unit eigenvector $v_2$ for the second largest eigenvalue of the adjacency matrix of $G$, lets $W$ be the $k$ vertices whose coordinates in $v_2$ are largest in absolute value (ties broken arbitrarily), and outputs the set of vertices with at least $3k/4$ neighbours in $W$. If $k \ge 10\sqrt n$ and $k = O(\sqrt{n \log n})$, then almost surely, that is with probability tending to $1$ as $n \to \infty$, the second eigenvector is unique up to scaling and Algorithm A outputs exactly $Q$.

## Proof sketch

Following Alon, Krivelevich and Sudakov, Section 2.2, let $z$ have $z_v = n - k$ on $Q$ and $z_v = -k$ off $Q$. By the Füredi-Komlós bound (their Lemma 2.2: almost surely every eigenvalue of $G(m, 1/2)$ but the largest has absolute value at most $\sqrt m + O(m^{1/3}\log m)$; compare the noise bound linked below), the eigenvalues of the adjacency matrix satisfy $\lambda_1 \ge (1/2 + o(1))n$ and $\lambda_i \le (1 + o(1))\sqrt n$ for $i \ge 3$ almost surely (Proposition 2.1), and from this Proposition 2.3 shows that almost surely some multiple of $v_2$ equals $z - d$ with $\|d\|_2^2 \le \|z\|_2^2/60 \le kn^2/60$, while Corollary 2.5 gives uniqueness of $v_2$ up to scaling. Each vertex outside $Q$ has a $\mathrm{Binomial}(k, 1/2)$ number of neighbours in $Q$, so Hoeffding's inequality and a union bound, as for the outside-degree bound linked below but with deviation $k/12$, show that all of them have fewer than $7k/12$ neighbours in $Q$ except with probability at most $n e^{-k/72}$, which tends to $0$ for $k \ge 10\sqrt n$. On these events, and for $n$ large enough that $12 \le k < n/6$, the deterministic recovery lemma outputs exactly $Q$.

## Depends on

- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)

## Proof depends on

- [Deterministic recovery from an approximate signal](planted-clique-deterministic-recovery.md)
- [Spectral norm of planted-clique noise is O(sqrt n)](../../../GraphTheory/random-graphs/planted-clique/planted-clique-noise-spectral-norm.md)
- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](../../../GraphTheory/random-graphs/planted-clique/planted-clique-outside-degrees.md)
- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998, Section 2 (Algorithm A in Section 2.1; Lemma 2.2, Proposition 2.3, Corollary 2.5 and the correctness argument in Section 2.2).
