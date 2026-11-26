# Exact count of one-component tree-child networks

**Definitions.** A rooted binary phylogenetic network on $n$ labelled leaves is **tree-child** if every non-leaf node has at least one child that is not a reticulation node (indegree $2$); the number $k$ of reticulation nodes satisfies $0 \le k \le n-1$. A tree-child network is **one-component** (OTC) if every reticulation node is immediately followed by a leaf. Let $\mathcal{OTC}_{n,k}$ be the set of OTCs with $n$ leaves and $k$ reticulations.

Pons and Batle encode tree-child networks by words: $\mathcal{C}_{n,k}$ is the set of words on letters $\omega_1,\dots,\omega_n$ in which $k$ letters occur three times and $n-k$ letters twice, such that in every prefix each letter $\omega_i$ that has occurred has occurred at least as often as every $\omega_j$ with $j > i$. Let $\mathcal{H}_{n,k} \subset \mathcal{C}_{n,k}$ consist of the words in which every letter immediately before the third occurrence of a letter is the second occurrence of that letter. Pons and Batle conjectured $|\mathcal{TC}_{n,k}| = \frac{n!}{(n-k)!}|\mathcal{C}_{n-1,k}|$ for all tree-child networks.

**Theorem.** There is a bijection between $\mathcal{OTC}_{n,k}$ and $\mathcal{H}_{n-1,k} \times \{1,\dots,n\}^{\underline{k}}$ (sequences of $k$ distinct labels), so

$$|\mathcal{OTC}_{n,k}| = \frac{n!}{(n-k)!}\,|\mathcal{H}_{n-1,k}|,$$

which is the Pons–Batle identity for the one-component class. Since $|\mathcal{H}_{n,k}| = \binom{n}{k}(2n-1)!!$,

$$|\mathcal{OTC}_{n,k}| = \frac{n!}{(n-k)!}\binom{n-1}{k}(2n-3)!! .$$

Moreover, if $R_n$ is the number of reticulations of an OTC drawn uniformly from all OTCs with $n$ leaves, then $(R_n - \mathbb{E}R_n)/\sqrt{\mathrm{Var}(R_n)} \to N(0,1)$ in distribution.

## Expansion

The bijection reads an OTC through a path decomposition: the word records the order in which the tree-like part of the network is traversed, the third occurrences mark where reticulation edges attach, and the $k$ distinct labels name the leaves hanging below the reticulations. Words in $\mathcal{C}_{n-1,0}$ encode rooted binary phylogenetic trees on $n$ leaves, of which there are $(2n-3)!!$. Removing the third occurrences from a word in $\mathcal{H}_{n,k}$ leaves a word in $\mathcal{C}_{n,0}$, and that word together with the set of $k$ letters immediately preceding the removed occurrences recovers the original; this bijection $\mathcal{H}_{n,k} \leftrightarrow \mathcal{C}_{n,0} \times \binom{[n]}{k}$ gives $|\mathcal{H}_{n,k}| = \binom{n}{k}(2n-1)!!$. The central limit theorem then follows from the explicit counts.

## Sources

- Michael Fuchs, Hexuan Liu and Guan-Ru Yu, "A Short Note on the Exact Counting of Tree-Child Networks", arXiv:2110.03842 (2021), Theorem 1, Lemmas 1–2, Corollary 1 and Theorem 2, <https://doi.org/10.48550/arXiv.2110.03842>.
