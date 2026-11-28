# Counting binary spinal tree-child networks

**Encoding.** A cover $\mathcal{C}$ of $[m]$ is *expanding* if, with $n = m - |\mathcal{C}| + 1$, no element of $[n]$ appears twice and for each $i = 1,\dots,|\mathcal{C}|$ the cover contains at least $i$ subsets of $[n+i-1]$. Labellable phylogenetic networks on $n$ leaves are in bijection with expanding covers; leaves are $1,\dots,n$ and the $i$-th set $C_i$ lists the children of the $i$-th non-leaf vertex. A network is *spinal* (its non-leaf vertices form one directed path from the root, the spine) iff its cover has exactly $i$ subsets of $[n+i-1]$ for each $i$. It is tree-child iff every set contains an integer appearing exactly once in the cover, and binary iff all sets have size 1 or 2 with $n+i$ appearing once when $|C_i| = 2$ and twice when $|C_i| = 1$.

**Proposition.** The number of spinal networks with $n$ leaves and cover size $|\mathcal{C}|$ is

$$S_{n,|\mathcal{C}|} = 2^{\binom{|\mathcal{C}|-1}{2}}\bigl(|\mathcal{C}|^n - (|\mathcal{C}|-1)^n\bigr).$$

This corrects the source's Proposition 3.2, which prints the exponent $\binom{|\mathcal{C}|-2}{2}$; its proof (Eq. (3)) multiplies the factors $2^{|\mathcal{C}|-i}$ for $i = 2,\dots,|\mathcal{C}|$, whose product is $2^{\binom{|\mathcal{C}|-1}{2}}$. For example, $|\mathcal{C}| = 3$ and $n = 2$ give $10$ spinal covers, not $5$.

**Theorem.** For $n > 1$ the number of binary spinal tree-child networks on $n$ labelled leaves with $k$ reticulations is

$$|\mathcal{STC}_{n,k}| = \frac{n!\,(n-2+k)!\,(n-1+3k)}{2^{k+1}\,k!\,(n-1-k)!},$$

with $|\mathcal{STC}_{1,k}| = 1$. Equivalently $|\mathcal{STC}_{n,k}| = n!\,|B_{n-1,k}| - \tfrac{n!}{2}|B_{n-2,k}|$, where $B_{m,k}$ is the set of partitions of $[m+k]$ into $m-k$ singletons and $k$ pairs, so that

$$|B_{m,k}| = \frac{(m+k)!}{2^k\,(m-k)!\,k!}\quad(0\le k\le m),\qquad |B_{m,k}| = 0\ \ (k>m)$$

(the Bessel-polynomial coefficients), with $|B_{0,0}| = 1$ (the empty partition). The source sets $|B_{0,k}| = 0$ for all $k$; at $n=2$, $k=0$ that gives $2$, whereas the closed formula, and the single cherry, give $1$. Summing over $0 \le k \le n-1$ gives all binary spinal TCNs, and $|\mathcal{STCS}_n| = \sum_k |B_{n-1,k}|$ counts their unlabelled shapes. For binary spinal stack-free networks,

$$|\mathcal{SSF}_{n,k}| = n!\,S_2(n-1+k,\,n-1) - \tfrac{n!}{2}\,S_2(n-2+k,\,n-2),$$

with $S_2$ the Stirling numbers of the second kind.

## Expansion

Each spine vertex $v$ has one non-spine edge to $w$: an $L$-vertex if $w$ is a leaf, a $P$-vertex if $w$ precedes $v$ on the spine, an $R$-vertex if it follows. In a binary spinal TCN every reticulation arises as an $R$-vertex immediately followed by an $L$-vertex together with one $P$-vertex pointing back to it, and the remaining sets are $L$-vertices. Counting the admissible category sequences of the cover gives the auxiliary numbers, and leaf labelling contributes the factor $n!$ with a correction for the symmetric final pair of leaves. Stack-free networks admit an extra category (an $R$-vertex followed by a $P$-vertex), which changes the count to Stirling numbers.

## Sources

- A. Francis, M. Hendriksen, "Counting spinal phylogenetic networks", *Bulletin of Mathematical Biology* 88(4) (2026), 61, Definition 2.2, Theorems 2.3-2.4 (cited), Proposition 3.2, Theorems 3.4-3.5, 3.8, 3.10-3.11 and 3.16, <https://doi.org/10.1007/s11538-026-01624-4> (preprint arXiv:2502.14223).
