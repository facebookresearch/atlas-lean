# Snowflakes are asymptotically certain in uniform binary trees

Let $\mathcal B(n)$ be the set of unrooted binary phylogenetic trees on the leaf set $[n]=\{1,\dots,n\}$, so $B(n)=|\mathcal B(n)|=(2n-5)!!=\frac{(2n-4)!}{(n-2)!\,2^{n-2}}$. A **snowflake** in $T\in\mathcal B(n)$ is a subtree consisting of a distinguished interior vertex $v$ (its centre) together with six interior vertices at distance $2$ from $v$; equivalently, $v$ is the centre of a snowflake if and only if every leaf of $T$ is at distance at least $3$ from $v$.

**Counting forests (Carter et al.).** For $n\ge k\ge 1$, the number of forests of $k$ rooted binary phylogenetic trees whose leaf sets partition a set of size $n$ is

$$N(n,k)=\frac{(2n-k-1)!}{(n-k)!\,(k-1)!\,2^{n-k}}.$$

**Mean number of centres.** Let $X_n$ be the number of snowflake centres in a tree drawn uniformly from $\mathcal B(n)$. For $n\ge 12$,

$$\mathbb E(X_n)=4\cdot\frac{(2n-13)!}{(2n-4)!}\cdot\frac{(n-2)!}{(n-12)!}\sim n\,2^{-7}.$$

**Theorem.** $\mathbb P(X_n=0)\to 0$ as $n\to\infty$: the fraction of binary phylogenetic trees on $n$ leaves that contain a snowflake tends to $1$. The same holds for the unrooted tree obtained by suppressing the root of a Yule–Harding tree.

## Proof depends on

- [Chebyshev's inequality](../../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Expansion

A pair $(T,v)$ with $v$ a snowflake centre is a choice of $12$ pendant rooted subtrees (a forest counted by $N(n,12)$) arranged around the snowflake skeleton in $12!/(2^9\cdot 3!)$ ways, which gives $\mathbb E(X_n)=|S(n)|/B(n)$. The first moment alone only gives $\liminf\mathbb P(X_n>0)\ge 2^{-7}$. For the theorem one shows $\mathbb E(X_n^2)\sim n^2 2^{-14}$: pairs of centres at distance at most $4$ contribute $O(n)$, and the remaining pairs factor through a forest count, so $\operatorname{Var}(X_n)=o(n^2)$ and Chebyshev's inequality concludes. For Yule–Harding trees the root split is uniform on $\{1,\dots,n-1\}$, so with high probability the root sits atop a complete balanced binary tree of depth $4$, which contains a snowflake once the root is suppressed. Snowflakes matter because the binary trees containing one are exactly those for which the smallest set of characters that are homoplasy-free only on $T$ has the maximum possible size $N(T)=4$ (Huber et al. 2023), so almost every large binary tree needs four such characters.

## Sources

- F. Bienvenu and M. Steel, "0–1 laws for pattern occurrences in phylogenetic trees and networks", Bulletin of Mathematical Biology 86(8) (2024) 94, <https://doi.org/10.1007/s11538-024-01316-x>, PMCID PMC11561131. Lemmas 1–2, Corollary 3, Theorem 4 and Proposition 5 (Section 2).
