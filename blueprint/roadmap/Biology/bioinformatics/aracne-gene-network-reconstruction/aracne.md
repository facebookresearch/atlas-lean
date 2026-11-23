# ARACNE gene network reconstruction

For a set $V$ of genes, a symmetric real function $I$ on pairs (the mutual informations) and a threshold $I_0$, the ARACNE network is the graph on $V$ in which $i$ and $k$ are adjacent if and only if

- $i \ne k$ and $I_0 < I(i, k)$, and
- every gene $j \notin \{i, k\}$ with $I_0 < I(i, j)$ and $I_0 < I(j, k)$ satisfies $\min(I(i, j), I(j, k)) \le I(i, k)$

(data-processing tolerance zero; Margolin et al. 2006).

## Sources

- A. A. Margolin, I. Nemenman, K. Basso, C. Wiggins, G. Stolovitzky, R. Dalla Favera and A. Califano, *ARACNE: an algorithm for the reconstruction of gene regulatory networks in a mammalian cellular context*, BMC Bioinformatics 7 (Suppl. 1) (2006), S7.
