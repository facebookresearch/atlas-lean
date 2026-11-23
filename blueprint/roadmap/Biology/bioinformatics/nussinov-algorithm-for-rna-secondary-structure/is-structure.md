# RNA secondary structure

For a sequence $s = s_0 \cdots s_{n-1}$, a complementarity relation on its alphabet and a natural number $m$ (the minimum hairpin size), a secondary structure is a finite set $P$ of pairs $(i, j)$ of natural numbers such that

- $i + m < j$ for every $(i, j) \in P$;
- for every $(i, j) \in P$, both $i, j < n$ and $s_i$ is complementary to $s_j$;
- distinct pairs share no position;
- no two pairs $(i, j), (k, l) \in P$ cross: never $i < k < j < l$

(Nussinov et al. 1978).

## Sources

- R. Nussinov, G. Pieczenik, J. R. Griggs and D. J. Kleitman, *Algorithms for loop matchings*, SIAM J. Appl. Math. 35 (1978), 68–82.
