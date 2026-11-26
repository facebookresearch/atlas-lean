# Weak partition connectivity gives generic full rank of intersection matrices

If the agreement hypergraph $(A_1, \dots, A_t)$ is $k$-weakly partition connected, then $M_{A,k}(\alpha)$ has full column rank for generic $\alpha$; and if a received word has $t$ distinct codewords of $\mathrm{RS}_k(\alpha)$ within radius $1 - R - \varepsilon$, then some sub-family of the agreement sets of size $O(1/\varepsilon)$ is $k$-weakly partition connected.

## Proof sketch

Full rank for generic points reduces, via a matroid-union style argument on the bipartite incidence structure of the hypergraph, to the GM-MDS theorem applied to an associated zero pattern; weak partition connectivity is exactly the Nash-Williams-Tutte type condition making the pattern satisfy the GM-MDS inequalities. The second statement is a counting argument: large total agreement $\sum_j |A_j| \ge t(R + \varepsilon)n$ forces the partition inequality for a small sub-family.

## Depends on

- [Agreement hypergraphs and reduced intersection matrices](agreement-hypergraphs-and-intersection-matrices.md)
- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Proof depends on

- [GM-MDS theorem (Lovett; Yildiz-Hassibi)](gm-mds-theorem.md)

## Sources

- Omar Alrabiah, Venkatesan Guruswami, Ray Li, "Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields", STOC (2024); arXiv:2304.09445.
- Zeyu Guo, Zihan Zhang, "Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets", FOCS (2023); arXiv:2304.01403.
