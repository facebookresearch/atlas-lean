# Coprime sampling of both genomes finds every long maximal exact match

**Problem.** Given a reference $R = R_0 \cdots R_{n_1 - 1}$ and a query $Q = Q_0 \cdots Q_{n_2 - 1}$, a maximal exact match (MEM) is a pair of equal substrings $R_{a \ldots a+\ell-1} = Q_{b \ldots b+\ell-1}$ that cannot be extended by one symbol to the left or to the right. The task is to report all MEMs of length $\ell \ge L$. A seed-and-extend method fixes a seed length $K \le L$, samples $K$-mers from $R$ every $k_1$ positions into a hash table, scans $Q$ every $k_2$ positions, looks each sampled query $K$-mer up, and extends the hits left and right.

**Proposition (number-theoretic core).** Let $k_1, k_2$ be coprime positive integers and $r_1 \in \{0, \dots, k_1 - 1\}$. For every $r \in \{0, \dots, k_2 - 1\}$ the set

$$\mathcal{S} = \{\, i k_1 + r_1 : i = 0, 1, \dots, k_2 - 1 \,\}$$

contains an element of the form $j k_2 + r$ with $j \ge 0$.

**Corollary (correctness of copMEM sampling).** If $\gcd(k_1, k_2) = 1$ and

$$k_1 k_2 \le L - K + 1,$$

then every MEM of length at least $L$ contains a pair of aligned $K$-mer occurrences, one starting at a sampled position of $R$ (a multiple of $k_1$) and the other at the corresponding sampled position of $Q$ (a multiple of $k_2$). Hence extending all seed hits reports every MEM of length $\ge L$, while only $n_1/k_1$ reference and $n_2/k_2$ query $K$-mers are processed. The single-genome scheme (step $L - K + 1$ in $R$, step $1$ in $Q$) is the case $k_2 = 1$.

## Expansion

The residues $(i k_1 + r_1) \bmod k_2$, $i = 0, \dots, k_2 - 1$, are pairwise distinct: equality of two of them would give $k_2 \mid (v - u)k_1$ with $0 < v - u < k_2$, impossible when $\gcd(k_1, k_2) = 1$. So they exhaust all $k_2$ residues. For the corollary, a MEM of length $\ell \ge L$ has $\ell - K + 1 \ge k_1 k_2$ aligned $K$-mer start offsets $t = 0, \dots, \ell - K$, i.e. aligned pairs $(a + t, b + t)$. Among the $k_2$ consecutive reference-sampled offsets inside the first $k_1 k_2$ positions, the proposition (with $r_1 \equiv -a \bmod k_1$ and $r \equiv -b \bmod k_2$) provides one whose query partner is also sampled. Coprimality is essential: with a common factor some residue classes are never paired and MEMs can be missed.

## Sources

- S. Grabowski and W. Bieniecki, "copMEM: Finding maximal exact matches via sampling both genomes", arXiv:1805.08816 (2018), Methods section and Proposition 1, <https://doi.org/10.48550/arXiv.1805.08816>.
