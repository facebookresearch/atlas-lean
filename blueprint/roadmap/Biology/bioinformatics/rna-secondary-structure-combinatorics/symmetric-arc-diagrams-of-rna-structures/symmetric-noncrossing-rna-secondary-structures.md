# Symmetric noncrossing RNA secondary structures

**Setting.** A simple RNA secondary structure on $n$ nucleotides is a noncrossing arc diagram on nodes $1,\dots,n$ in which each node lies on at most one arc and no arc joins adjacent nodes; equivalently a $3412$-avoiding involution of $[n]$ with no transposition $(i,i+1)$. Their number $S_n$ ($1,1,2,4,8,17,37,\dots$) satisfies Waterman's recursion $S_n=S_{n-1}+\sum_{j=3}^nS_{j-2}S_{n-j}$ for $n\ge3$ with $S_0=S_1=S_2=1$. A diagram is **symmetric** if its involution $\sigma$ is invariant under the reverse complement $\sigma^{rc}(i)=n+1-\sigma(n+1-i)$, i.e. the diagram equals its mirror image. Let $R_n$ count symmetric simple structures ($1,1,2,2,4,5,9,12,21,29,\dots$).

**Theorem 2.2.** With $R_0=R_1=R_2=1$, $R_3=R_4=2$ and $R_5=4$,

$$
R_n=2R_{n-2}+\sum_{j=3}^{\lfloor n/2\rfloor}S_{j-2}R_{n-2j}\qquad(n\ge6).
$$

**Proposition 2.4.** For $n\in\mathbb N$, $R_{2n+1}=R_{2n}+R_{2n-1}$ and $R_{2n}=R_{2n-1}+R_{2n-2}-S_{n-1}$.

**Motzkin-type diagrams.** If nonnesting arcs may share an endpoint (noncrossing partitions of $[n]$ with no block containing consecutive integers), let $M_n$ denote the number of these diagrams on $n$ nodes ($M_1=M_2=1, M_3=2, M_4=4, M_5=9, M_6=21,\dots$, i.e. the shifted Motzkin number usually indexed $M_{n-1}$) and correspond bijectively, preserving symmetry, to Motzkin paths with $n-1$ steps. The number $L_n$ of symmetric such diagrams satisfies, with $L_0=L_1=L_2=1$ and $L_3=L_4=2$,

$$
L_n=2L_{n-2}+\sum_{j=3}^{\lfloor(n+1)/2\rfloor}M_{j-2}L_{n+2-2j}\qquad(n>4)\quad\text{(Theorem 4.2)}.
$$

With $a_0=1$ and $a_n=L_{2n-1}$, one has $a_n=\sum_{j=0}^{n-1}M_{j+1}a_{n-1-j}$ and $a_{n+1}=3a_n-M_n$ for $n\ge 1$ (Theorem 4.4), and $L_{2n-1}$ equals the number of base-$3$ numbers with $n$ digits and digit sum $n$ (Theorem 4.6).

**Rarity of symmetry.** With $\varphi=(1+\sqrt5)/2$, the known asymptotics $S_n\sim c_1(1+\varphi)^n n^{-3/2}$ and $R_n\sim c_2\varphi^nn^{-1/2}$ ($c_1\approx1.104$, $c_2\approx0.863$) give $R_n/S_n\sim(c_2/c_1)\,n\,\varphi^{-n}$, and $L_n/M_n\le(\sqrt{8/3}+o(1))\,n\,3^{-n/2}$, with equality in the limit along odd $n$: a random structure of length $n$ is symmetric with exponentially small probability.

## Depends on

- [Waterman's recursion](../../mccaskill-partition-function-for-rna-folding/waterman-number.md)

## Expansion

A symmetric diagram is determined by its left half together with the arcs crossing the middle, which must be nested and centered. For $R_n$, either the first and last nodes are both isolated ($R_{n-2}$ ways), or they are joined by an arc ($R_{n-2}$ ways), or node $1$ is joined to some node $j\ge3$ in the left half: then any structure of length $j-2$ sits under that arc, its mirror image sits under the mirror arc, and any symmetric structure of length $n-2j$ fills the middle. The odd-length identity removes the isolated middle node or the short arc around it. For Motzkin diagrams the bijection to Motzkin paths sends symmetric diagrams to palindromic paths, which are determined by their left factors; encoding steps by digits $2,1,0$ maps left factors to ternary numbers, and a further rearrangement gives the digit-sum characterization.

## Sources

- Juan B. Gil and Luis E. Lopez, "Enumeration of symmetric arc diagrams", arXiv (2022), Section 2 "Symmetric noncrossing arc diagrams" (Theorem 2.1 quoted from Waterman, Theorem 2.2, Proposition 2.4), Section 4 "Symmetric arc diagrams of Motzkin type" (Theorems 4.2, 4.4 and 4.6) and Section 6 "Final remarks" (asymptotic ratios), <https://doi.org/10.48550/arXiv.2203.10589> Published version: Involve 16 (2023) 107-126, <https://doi.org/10.2140/involve.2023.16.107>.
