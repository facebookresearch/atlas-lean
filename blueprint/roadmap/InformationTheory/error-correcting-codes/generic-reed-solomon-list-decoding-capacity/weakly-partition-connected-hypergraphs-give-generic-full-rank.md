# Weak partition connectivity gives generic full rank of intersection matrices

Let $t \ge 2$. If the agreement hypergraph $(A_1, \dots, A_t)$ is $k$-weakly partition connected, then $M_{A,k}(\alpha)$ has full column rank for generic $\alpha$. Conversely, bad lists give such hypergraphs: if $y, c^{(1)}, \dots, c^{(L+1)} \in \mathbb{F}^n$ satisfy $\sum_{j=1}^{L+1} d(y, c^{(j)}) \le L(n - k)$, then for some $J \subseteq [L+1]$ with $|J| \ge 2$ the agreement hypergraph $(A_j)_{j \in J}$, $A_j = \{i : c^{(j)}_i = y_i\}$, is $k$-weakly partition connected. In particular this applies to any $t = L + 1 \ge (1 - R)/\varepsilon$ codewords of $\mathrm{RS}_k(\alpha)$, $R = k/n$, within radius $1 - R - \varepsilon$ of $y$, since then $\sum_j d(y, c^{(j)}) \le t(1 - R - \varepsilon)n \le (t - 1)(1 - R)n$.

## Proof sketch

Full rank for generic points reduces, via a matroid-union style argument on the bipartite incidence structure of the hypergraph, to the GM-MDS theorem applied to an associated zero pattern; weak partition connectivity is exactly the Nash-Williams-Tutte type condition making the pattern satisfy the GM-MDS inequalities. The second statement is a counting argument: the distance bound gives $\sum_{i} (|e_i| - 1)_+ \ge Lk$, where $e_i = \{j : i \in A_j\}$, and an inclusion-minimal $J$ with $|J| \ge 2$ and $\sum_i (|e_i \cap J| - 1)_+ \ge (|J| - 1)k$ satisfies the partition inequality for every partition of $J$.

## Depends on

- [Agreement hypergraphs and reduced intersection matrices](agreement-hypergraphs-and-intersection-matrices.md)
- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Proof depends on

- [GM-MDS theorem (Lovett; Yildiz-Hassibi)](gm-mds-theorem.md)

## Sources

- Omar Alrabiah, Venkatesan Guruswami, Ray Li, "Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields", STOC (2024); arXiv:2304.09445v4 (Lemma 2.3 and Theorem 2.10).
- Zeyu Guo, Zihan Zhang, "Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets", FOCS (2023); arXiv:2304.01403.
