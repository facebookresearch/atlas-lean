# Number of k-cut rearrangements of a circular genome

**Setting.** A signed, uni-chromosomal circular genome with $n$ oriented regions is represented in the position paradigm by a signed permutation $\sigma$ in the hyperoctahedral group $H_n \le \mathrm{Sym}(\{1, \dots, n, \bar 1, \dots, \bar n\})$. Rotations and flips of the circle form a dihedral subgroup $\mathcal{D}_n \le H_n$ of order $2n$, so a genome is a coset $\mathcal{D}_n\sigma$, and a rearrangement $\alpha \in H_n$ (a map from positions to positions) is taken up to the left action of $\mathcal{D}_n$: two rearrangements $\alpha, d\alpha$ with $d \in \mathcal{D}_n$ produce the same genome. With $c = (1, \dots, n)(\bar n, \dots, \bar 1)$ the rotation, the set of cuts of $\alpha$, the positions $i$ such that $\alpha$ separates positions $i$ and $i+1 \pmod n$, is

$$\mathrm{cuts}(\alpha) = [n] \setminus \mathrm{Fix}\big([\alpha, c]\big), \qquad [\alpha, c] = \alpha^{-1}c^{-1}\alpha c,$$

and it depends only on the coset $\mathcal{D}_n\alpha$. Signed inversions are exactly the rearrangements with $|\mathrm{cuts}(\alpha)| = 2$, signed transpositions those with $|\mathrm{cuts}(\alpha)| = 3$, and block interchanges those with $|\mathrm{cuts}(\alpha)| \in \{3, 4\}$.

**Proposition.** For $2 \le k \le n$, the number of cosets $\mathcal{D}_n\alpha \in H_n/\mathcal{D}_n$ with $|\mathrm{cuts}(\alpha)| = k$ is

$$\binom{n}{k}\,a(k), \qquad a(k) = (-1)^k + \sum_{i=0}^{k-1} (-1)^{k-1+i}\binom{k}{i+1}\, i!\, 2^i,$$

where $a(k)$ is OEIS sequence A061714, the number of pure $k$-opt moves of a cyclic tour.

## Proof sketch

Choosing which $k$ of the $n$ junctions are cut gives $\binom{n}{k}$. The $k$ resulting segments must then be reassembled into a circle, each segment possibly reversed, so that none of the $k$ original adjacencies is restored (otherwise fewer cuts would suffice). Fixing one segment, the others can be arranged in $(k-1)!$ orders with $2^{k-1}$ orientations; inclusion–exclusion over restored adjacencies yields the alternating sum $a(k)$, which coincides with the count of pure $k$-opt moves known from the travelling-salesman literature. For example $a(2) = 1$ (the only 2-cut move is an inversion) and $a(3) = 4$.

## Sources

- Joshua Stevenson, Venta Terauds and Jeremy Sumner, "Rearrangement Events on Circular Genomes", *Bulletin of Mathematical Biology* 85 (2023), 107, <https://doi.org/10.1007/s11538-023-01209-5>. Preprint version: arXiv:2202.01968 (2022), Section 4 (definition of the cut set, its commutator characterization, the classification lemma for inversions, transpositions and block interchanges, and the proposition counting $k$-cut cosets), <https://doi.org/10.48550/arXiv.2202.01968>.
