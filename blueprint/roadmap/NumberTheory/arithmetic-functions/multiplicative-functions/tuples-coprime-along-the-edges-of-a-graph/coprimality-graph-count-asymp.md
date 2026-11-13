# Asymptotic count of tuples coprime along the edges of a graph

Let $k \ge 2$ and let $E$
be a set of pairs $(i, j)$ with $0 \le i < j < k$, the edge set of a graph $G$ on the vertices
$0, \dots, k-1$. Let $d_G$ be the maximum degree of $G$, that is, the largest number of pairs in
$E$ that contain a single vertex; let $\delta_G$ be the coprimality indicator and $A_G$ the
coprimality density of $G$. Then there is a real constant $C$ such that for every integer
$N \ge 2$,

$$\Bigl|\sum_{n \in \{1, \dots, N\}^k} \delta_G(n) - A_G N^k\Bigr| \le C N^{k-1} (\log N)^{d_G}.$$

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`).
