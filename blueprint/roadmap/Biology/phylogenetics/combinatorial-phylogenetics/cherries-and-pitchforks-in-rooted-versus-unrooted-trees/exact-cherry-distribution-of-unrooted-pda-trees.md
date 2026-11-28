# Exact cherry distribution of unrooted PDA trees

Let $B_n$ be the number of cherries (pairs of leaves adjacent to a common vertex) and $A_n$ the number of pitchforks (subtrees with exactly three leaves) of a random unrooted binary phylogenetic tree with $n$ leaves. Under the **PDA model** the tree is uniform over all $(2n-5)!!$ unrooted trees; under the **YHK model** it is grown by attaching each new leaf to a uniformly chosen pendant edge.

**Theorem (PDA).** For $n\ge4$ and $1<k<n$,

$$\mathbb{P}(B_{n+1}=k)=\frac{n+2k-3}{2n-3}\,\mathbb{P}(B_n=k)+\frac{n-2k+2}{2n-3}\,\mathbb{P}(B_n=k-1),$$

and for $2\le k\le n/2$

$$\mathbb{P}_{\mathrm{PDA}}(B_n=k)=\frac{n!\,(n-2)!\,(n-4)!\,2^{n-2k}}{(n-2k)!\,(2n-4)!\,k!\,(k-2)!}.$$

Hence

$$\mathbb{E}_{\mathrm{PDA}}(B_n)=\frac{n(n-1)}{2(2n-5)},\qquad \operatorname{Var}_{\mathrm{PDA}}(B_n)=\frac{n(n-1)(n-4)(n-5)}{2(2n-5)^2(2n-7)},$$

and $\mathbb{E}_{\mathrm{PDA}}(A_n)=\dfrac{n(n-1)(n-2)}{2(2n-5)(2n-7)}$ for $n\ge6$.

**Theorem (YHK).** For $n\ge4$ and $1<k<n$,

$$\mathbb{P}(B_{n+1}=k)=\frac{2k}{n}\,\mathbb{P}(B_n=k)+\frac{n-2k+2}{n}\,\mathbb{P}(B_n=k-1),$$

with $\mathbb{E}_{\mathrm{YHK}}(B_n)=\frac{n}{3}+\frac{4}{(n-1)(n-2)}$ ($n\ge4$), $\operatorname{Var}_{\mathrm{YHK}}(B_n)=\frac{2n}{45}-\frac{4(n^2-3n+14)}{3(n-1)^2(n-2)^2}$ ($n\ge5$), and $\mathbb{E}_{\mathrm{YHK}}(A_n)=\frac{n}{6}+\frac{4(2n-3)}{(n-1)(n-2)(n-3)}$ ($n\ge6$).

**Theorem (log-concavity).** For $n\ge4$ and $2\le k\le n/2$ the unrooted cherry probability mass functions $\sigma_n(k)=\mathbb{P}_{\mathrm{PDA}}(B_n=k)$ and $\tau_n(k)=\mathbb{P}_{\mathrm{YHK}}(B_n=k)$ are strictly log-concave: $\sigma_n(k)^2>\sigma_n(k-1)\sigma_n(k+1)$ and likewise for $\tau_n$. For $n>8$, with $\nabla(n)=\lceil n/4\rceil$, $\sigma_n(k-1)<\sigma_n(k)$ for $2\le k<\nabla(n)$ and $\sigma_n(k)>\sigma_n(k+1)$ for $\nabla(n)\le k\le n/2$ (Theorem 7). Moreover $\tau_n(k)/\sigma_n(k)$ is strictly increasing in $k$ for $n\ge6$ (Theorem 8).

## Expansion

An unrooted tree on $n+1$ leaves arises from one on $n$ leaves by subdividing one of its $2n-3$ edges and attaching the new leaf. Attaching to a pendant edge of a cherry leaf keeps the cherry count; attaching to a pendant edge of a non-cherry leaf creates a cherry; attaching to an interior edge keeps it. Counting edges of each kind ($2k$ cherry pendant edges, $n-2k$ other pendant edges, $n-3$ interior edges) gives the PDA recursion, where all $2n-3$ edges are equally likely, and the YHK recursion, where only the $n$ pendant edges are used. The closed form solves the PDA recursion, and log-concavity follows by induction from the recursions; the joint recursions for $(A_n,B_n)$ give the pitchfork moments.

## Sources

- K. P. Choi, A. Thompson, T. Wu, "On cherry and pitchfork distributions of random rooted and unrooted phylogenetic trees", arXiv:2002.12643 (2020), Theorems 1, 3, 4, 6, 7 and 8, Corollaries 1–2, Propositions 2 and 4, <https://doi.org/10.48550/arXiv.2002.12643>.
