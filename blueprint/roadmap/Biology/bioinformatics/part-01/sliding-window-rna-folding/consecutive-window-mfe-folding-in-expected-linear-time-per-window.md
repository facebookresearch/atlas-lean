# Consecutive-window MFE folding in expected O(NL) time

Let $s = s_1 \cdots s_N$ be an RNA sequence. In the nearest-neighbour minimum free energy (MFE) recursions, $V(i,j)$ is the MFE of $s_i \cdots s_j$ over structures in which $s_i$ pairs with $s_j$ (a **closed structure**; $V = +\infty$ if they cannot pair), and

$$W(i, j) = \min\Big\{ V(i, j),\ \min_{i \le k < j} \big( W(i, k) + W(k+1, j) \big) \Big\}$$

is the MFE of $s_i \cdots s_j$; internal-loop sizes are bounded by a constant, so the $W$ recursion is the cubic bottleneck. The **consecutive windows folding problem** asks, for a window length $L < N$, for $W(i, i + L - 1)$ for every window start $i$.

**Triangle inequality and candidates.** $W(i, j') \le W(i, j) + W(j+1, j')$ for $i \le j < j'$. Hence every optimal split can be taken with a closed left part, $W(i,j) = \min\{ V(i,j), \min_{i \le k < j} V(i,k) + W(k+1, j)\}$, and if $V(i,j) \ge V(i,k) + W(k+1, j)$ for some $k < j$, then $V(i, j) + W(j+1, j') \ge V(i,k) + W(k+1, j')$ for every $j' > j$. Call $j$ a **candidate** in row $i$ if $V(i,j) < V(i,k) + W(k+1,j)$ for all $i \le k < j$; only candidates need be considered as split points:

$$W(i, j) = \min\Big\{ V(i,j),\ \min_{k \text{ candidate},\ k < j} V(i,k) + W(k+1, j) \Big\}.$$

**Theorem.** Computing the $L$-wide band of $W$ in decreasing row order and increasing column order, with the candidate list of row $i$ restarted at each row and extended by $j$ whenever $V(i,j) < W(i,j)$, solves the consecutive windows folding problem in $O(N L)$ expected time and $O(N + L^2)$ space, under the polymer-folding assumption that the optimal folding of a segment of length $q$ is closed with probability $b\,q^{-c}$ for some $c > 1$. A traceback of any window costs $O(L)$ additional time.

This improves the naive $O(N L^3)$ (fold each window independently) and the $O(N L^2)$ band algorithm.

## Depends on

- [Zuker minimum free energy](../../zuker-s-minimum-free-energy-algorithm/zuker-mfe.md)

## Expansion

Every window $[i, i+L-1]$ uses only entries $W(i', j')$ with $i \le i' \le j' \le i + L - 1$, all inside the band $j - i < L$ of the full $N \times N$ table, so filling the band row by row from the bottom answers every window. The triangle inequality is what makes a dominated split point stay dominated for all larger $j'$, so a row's candidate list never needs to be revisited. Under the polymer model the probability that column $j$ is a candidate in row $i$ is at most $b(j - i)^{-c}$, so the expected list length in a window is $\psi(L) = b\sum_{q=1}^{L} q^{-c} \le b\,\zeta(c) = O(1)$. Each of the $O(NL)$ band entries therefore costs $O(1)$ expected time, and only an $L \times L$ block of the band must be kept in memory at once. Measured on genomic sequences, the running time is consistent with the $O(L)$ speedup.

## Sources

- Y. Horesh, Y. Wexler, I. Lebenthal, M. Ziv-Ukelson and R. Unger, "RNAslider: a faster engine for consecutive windows folding and its application to the analysis of genomic folding asymmetry", BMC Bioinformatics 10 (2009) 76, Eqs. (1)–(4), (2a), (3a), Definitions 1–3, Lemma 1, Theorems 1–3, <https://doi.org/10.1186/1471-2105-10-76>, PMCID PMC2682796.
