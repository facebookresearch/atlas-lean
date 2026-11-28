# Cherry perfect phylogenies maximizing the number of compatible trees

**Setting.** For $n\ge2$ and $1\le x\le n-1$ let $B_x(n)=(x,n-x)$ be the binary perfect phylogeny consisting of a root with two haplotype leaves of counts $x$ and $n-x$. Let $b_x(n)$, $b'_x(n)$, $b''_x(n)$ denote the numbers of ranked unlabeled tree shapes, ranked labeled trees, and unranked labeled trees, respectively, with $n$ leaves compatible with $B_x(n)$ (for the labeled counts the two leaves carry fixed disjoint sets of $x$ and $n-x$ sequences). Let $e_i=R_{i+1}$ be the number of ranked tree shapes with $i$ internal nodes (Euler zigzag numbers), with exponential generating function $\sum_i e_iz^i/i!=\sec z+\tan z$.

**Theorem.**

1. Among the sequences $b_1(n),b_2(n),b_3(n),\dots$, the sequence $b_2(n)$ has the fastest asymptotic growth as $n\to\infty$, and

    $$b_2(n)\sim 2\Bigl(\frac{2}{\pi}\Bigr)^{n-2}(n-2)!.$$

2. For fixed $n\ge2$, $b'_x(n)=\binom{n-2}{x-1}L_xL_{n-x}=\dfrac{n!\,(n-2)!}{2^{n-2}}\binom{n}{x}^{-1}$, so $b'_1(n)$ is the largest among $b'_1(n),\dots,b'_{\lfloor n/2\rfloor}(n)$.
3. For fixed $n\ge2$, $b''_x(n)=X_xX_{n-x}$ with $b''_{x+1}(n)/b''_x(n)=\dfrac{2x-1}{2n-2x-3}\le1$ for $1\le x\le\frac{n-1}{2}$, so $b''_1(n)$ is the largest among $b''_1(n),\dots,b''_{\lfloor n/2\rfloor}(n)$.

## Depends on

- [Recursive enumeration of tree shapes compatible with a binary perfect phylogeny](recursive-enumeration-of-tree-shapes-compatible-with-a-binary-perfect-phylogeny.md)

## Expansion

For $(x+1,n-x+1)$ with $n>2x$ the ranked recursion gives $\binom{n}{x}e_xe_{n-x}=n!\,q_xq_{n-x}$ with $q_i=e_i/i!$. Singularity analysis of $\sec z+\tan z$ at $z=\pi/2$ gives $q_i\sim2(2/\pi)^{i+1}$, while for fixed $x$ one has the exact series $q_x=2(2/\pi)^{x+1}c_x$ with $c_x=\sum_{k\ge0}(-1)^k(2k+1)^{-(x+1)}\le1$ for even $x$ and $c_x=(1-2^{-(x+1)})\zeta(x+1)$ for odd $x$. Thus $q_xq_{n-x}\sim4(2/\pi)^{n+2}c_x$, and $c_1=\tfrac34\zeta(2)=\pi^2/8\approx1.234$ beats $c_x<\zeta(3)\approx1.202$ for odd $x\ge3$ and $c_x\le1$ for even $x$; the maximizing internal-node split $x=1$ is the haplotype count $2$. For $n=10$ the asymptotic formula gives $2175.66$ against the exact $b_2(10)=2176$. In the labeled cases the closed forms are monotone in $x$, so a singleton haplotype separated from the rest is the least constraining cherry.

## Sources

- Julia A. Palacios, Anand Bhaskar, Filippo Disanto and Noah A. Rosenberg, "Enumeration of binary trees compatible with a perfect phylogeny", Journal of Mathematical Biology 84 (2022), 54, <https://doi.org/10.1007/s00285-022-01748-w>; numbering as in arXiv:2108.04849: Section 3: Propositions 11, 13, 14, 16, 17.
