# Order min hash is locality-sensitive for the edit similarity

**Definitions.** For sequences $S_1, S_2$ of length $n$ over an alphabet $\Sigma$, the *edit dissimilarity* is $E_d(S_1, S_2) = \mathrm{ed}(S_1, S_2)/n$ and the *edit similarity* $E_s = 1 - E_d$. A family $\mathcal H$ of hash functions is *$(s_1, s_2, p_1, p_2)$-sensitive* for a similarity $s$ (with $s_1 \ge s_2$, $p_1 \ge p_2$) if for $h$ drawn uniformly from $\mathcal H$: $s(S_1, S_2) \ge s_1 \Rightarrow \Pr[h(S_1) = h(S_2)] \ge p_1$ and $s(S_1, S_2) \le s_2 \Rightarrow \Pr[h(S_1) = h(S_2)] \le p_2$.

Let $n_k = n - k + 1$. The *uniquified k-mer set* $M^w_k(S)$ contains, for every position $i$, the pair $(m, o)$ where $m = S[i : i+k)$ and $o$ is the number of earlier occurrences of $m$ in $S$. For a permutation $\pi$ of $\Sigma^k \times [n]$, let $h^w_{\ell,\pi}(S)$ be the vector of the $\ell$ smallest elements of $M^w_k(S)$ under $\pi$, *listed in the order in which their k-mers occur in $S$*, and $h_{\ell,\pi}(S)$ the same vector with occurrence numbers dropped. The *order min hash* (OMH) family is $\{h_{\ell, \pi}\}$ with $\pi$ uniform.

**Theorem 1 ($\ell = 1$).** OMH with $\ell = 1$ is a locality-sensitive hash for the weighted Jaccard similarity: $\Pr[h_{1,\pi}(S_1) = h_{1,\pi}(S_2)] = J\bigl(M^w_k(S_1), M^w_k(S_2)\bigr)$.

**Theorem 2.** For every $\ell \in [2, n - k]$ and $1 > s_1 \ge s_2 > 0$, OMH is $(s_1, s_2, p_1, p_2)$-sensitive for the edit similarity, with

$$p_1 = \binom{n - n(k+2)(1 - s_1)}{\ell} \Big/ \binom{n_k + kn(1 - s_1)}{\ell}, \qquad p_2 \le \Bigl(\frac{n_k}{L}\Bigr)^{\ell} \binom{L}{\ell} \Big/ \binom{n_k}{\ell}, \quad L = n s_2 - k + 1 .$$

**Lemma (patience sorting).** For integers $n \ge i \ge \ell$, a sequence of length $n$ whose longest increasing subsequence has length at most $i$ has at most $(n/i)^{\ell}\binom{i}{\ell}$ increasing subsequences of length $\ell$, and this bound is tight.

## Depends on

- [Unit-cost edit distance is a Needleman–Wunsch instance](../../sequence-alignment/pairwise-sequence-alignment/edit-distance-distance-eq-neg-nw-score.md)

## Expansion

Each element of $M^w_k(S_1) \cup M^w_k(S_2)$ is equally likely to be among the $\ell$ smallest under a random permutation, so collision probabilities are ratios of binomial coefficients. *Lower bound*: an alignment with at most $n(1-s_1)$ errors leaves at least $n_k - kn(1-s_1)$ k-mers in aligned stretches (each error destroys at most $k$ consecutive k-mers); subtracting the at most $2n(1-s_1) - k + 1$ aligned k-mers whose occurrence numbers may disagree leaves $n - n(k+2)(1-s_1)$ shared uniquified k-mers, appearing in the same relative order in both sequences, while the union has at most $n_k + kn(1-s_1)$ elements; drawing all $\ell$ from the shared ones forces a collision. *Upper bound*: a collision requires the $\ell$ chosen k-mers to form a common subsequence of the two k-mer sequences; if $E_s \le s_2$ the longest common subsequence $L$ satisfies $s_2 \ge (L + k - 1)/n$, and the patience-sorting lemma (stacks of decreasing cards, with the number of stacks equal to the longest increasing subsequence and the count maximized by equal stack heights) bounds the number of such $\ell$-subsets. At $\ell = 1$ order is ignored and OMH reduces to minHash on weighted k-mer sets; at $\ell = n_k$ a collision means equality of the sequences. Jaccard similarity fails as a proxy: two de Bruijn sequences have identical k-mer content but can have edit similarity far below that of random sequences.

## Sources

- G. Marçais, D. DeBlasio, P. Pandey, C. Kingsford, "Locality-sensitive hashing for the edit distance", Bioinformatics (2019), Section 2.3 (definition of OMH and uniquified k-mers; Theorem 1, Eq. 5; Theorem 2), Section 3 (Lemma 1, Eq. 6; Lemma 2, Eq. 9; Eq. 13; Lemma 3) and Section 2.2 (counterexamples for Jaccard and Hamming similarities). <https://doi.org/10.1093/bioinformatics/btz354> (PMC6612865).
