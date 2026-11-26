# Gapped k-mer kernel and its mismatch-profile formula

Fix an alphabet $\mathcal{A}$ of size $b$ (for DNA $b = 4$), a word length $l$ and a number of informative positions $k$ with $1 \le k \le l$. A **gapped $k$-mer** is a pair $(P, w)$ where $P \subseteq \{1, \dots, l\}$ with $|P| = k$ is a set of informative positions and $w \in \mathcal{A}^P$ assigns a letter to each of them; the remaining $l - k$ positions are gaps (wildcards). There are $M = \binom{l}{k} b^k$ gapped $k$-mers. For a sequence $S$ with $n = |S| - l + 1$ full $l$-mers $u_1, \dots, u_n$ (its length-$l$ windows), let $f_{(P,w)}(S)$ be the number of pairs (window $i$, gapped $k$-mer $(P, w)$) such that $u_i$ restricted to $P$ equals $w$, and let $f(S) \in \mathbb{N}^M$ be the feature vector. The **gkm-kernel** is the normalized inner product

$$K(S_1, S_2) = \frac{\langle f(S_1), f(S_2) \rangle}{\sqrt{\langle f(S_1), f(S_1) \rangle \, \langle f(S_2), f(S_2) \rangle}} \in [0, 1], \qquad K(S, S) = 1 .$$

**Proposition (mismatch-profile formula).** For two $l$-mers $u, v$ differing at exactly $m$ positions ($0 \le m \le l$), the number of gapped $k$-mers matched by both is

$$h_m = \binom{l - m}{k}$$

(zero when $l - m < k$). Consequently, if $u^{(1)}_i$ and $u^{(2)}_j$ are the $l$-mers of $S_1$ and $S_2$ and $N_m(S_1, S_2)$ is the number of pairs $(i, j)$ whose $l$-mers have exactly $m$ mismatches (the **mismatch profile**),

$$\langle f(S_1), f(S_2) \rangle = \sum_{i=1}^{n_1} \sum_{j=1}^{n_2} h\big(u^{(1)}_i, u^{(2)}_j\big) = \sum_{m=0}^{l - k} N_m(S_1, S_2)\, \binom{l - m}{k} .$$

Properties:

- the kernel is a Gram matrix of explicit features, hence positive semidefinite, and is usable in any kernel SVM;
- evaluation needs only the $l$-mer pairs, not the $M$ features: the double sum costs $O(n_1 n_2)$ mismatch counts, and pairs with more than $l - k$ mismatches contribute nothing;
- the coefficients decrease in $m$, so near-identical $l$-mers dominate while $l$-mers with a few mismatches still contribute, which smooths sparse $k$-mer counts; for $k = l$ the kernel reduces to the normalized contiguous $l$-mer spectrum kernel ($h_0 = 1$, $h_m = 0$ for $m \ge 1$).

## Expansion

Expanding the inner product as a sum over feature coordinates and exchanging sums gives $\sum_{(P,w)} f_{(P,w)}(S_1) f_{(P,w)}(S_2) = \sum_{i,j} \#\{(P, w) : u^{(1)}_i|_P = w = u^{(2)}_j|_P\}$. For fixed $i, j$ and fixed $P$ there is at most one admissible $w$, and it exists exactly when the two $l$-mers agree on $P$, that is, when $P$ avoids the $m$ mismatch positions; there are $\binom{l-m}{k}$ such $P$. Grouping pairs by $m$ yields the profile formula. Computing $N_m$ for all training pairs is done either by direct pairwise mismatch counting or simultaneously with a $k$-mer tree; truncating the sum at a maximum mismatch number gives a faster approximation. Unlike the wildcard kernel, the number of gaps is fixed at $l - k$ rather than summed over.

## Sources

- M. Ghandi, D. Lee, M. Mohammad-Noori and M. A. Beer, "Enhanced regulatory sequence prediction using gapped k-mer features", PLoS Computational Biology 10 (2014), e1003711, Results, Eqs. (1)–(4), <https://doi.org/10.1371/journal.pcbi.1003711> (PMC4102394).
