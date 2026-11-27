# Average-linear-time sparse distance computation for typing profiles

Let $P$ be a set of $d$ allelic typing profiles (for instance MLST or cgMLST allele vectors) of length $m$ over an integer alphabet $\Sigma$, $|\Sigma| = \sigma > 1$, and $0 < k < m$ a maximum Hamming distance. Distance-based phylogenetic methods such as goeBURST need only the pairs at distance at most $k$: goeBURST computes a minimum spanning forest of the graph $G = (P, \{(u,v) : H(u,v) \le k\})$ with lexicographic tie-breaking by locus-variant counts, a graphic-matroid greedy problem. Computing all pairwise distances costs $\Theta(md^2)$.

**Algorithm.** Concatenate the profiles into a string $s$ of length $md$, build its suffix array, LCP array and a constant-time range-minimum structure over LCP ($O(md)$ time and space). Split each profile into $k+1$ non-overlapping aligned blocks of length $L = \lfloor m/(k+1) \rfloor$; by the pigeonhole principle, two profiles at Hamming distance at most $k$ share at least one identical aligned block. Group suffixes starting at the same block index whose longest common prefix is at least $L$ (LCP clusters), and verify each candidate pair in $O(k)$ time with range-minimum queries on LCP that jump from mismatch to mismatch.

**Theorem 1.** If the profile letters are i.i.d. uniform over $\Sigma$, the algorithm reports all pairs at Hamming distance at most $k$ in $O(md)$ average-case time and space provided

$$k < \frac{(m - k - 1)\log\sigma}{\log(md)} .$$

**Theorem 2.** Under the same model, with the profiles indexed by a suffix tree, all profiles within distance $k$ of a query profile are found in $O(m)$ average-case time under the same condition on $k$ (worst case $O(md + m\log md)$).

## Expansion

The expected number of spurious candidate pairs is at most $B d/\sigma^{L}$, where $B = d\lfloor m/L\rfloor$ is the number of blocks, since two random aligned blocks agree with probability $\sigma^{-L}$. Each costs $O(k)$ to verify, giving $O\big(md + (md)^{2 - (m-k-1)\log\sigma / ((k+1)\log(md))}\big)$, which is linear exactly under the stated condition. In practice the LCP-cluster method is up to two orders of magnitude faster than naive all-pairs computation for goeBURST on large bacterial typing databases.

## Sources

- J. A. Carriço, M. Crochemore, A. P. Francisco, S. P. Pissis, B. Ribeiro-Gonçalves and C. Vaz, "Fast phylogenetic inference from typing data", Algorithms for Molecular Biology 13 (2018), Algorithms 1–2 and Theorems 1–2, <https://doi.org/10.1186/s13015-017-0119-7>, PMCID: PMC5815242.
