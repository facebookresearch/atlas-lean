# Brownian-excursion scaling function for tree-child networks

**Setting.** A binary phylogenetic network on $[n]=\{1,\dots,n\}$ is a finite directed acyclic graph with a root of in-degree $0$ and out-degree $1$, $n$ leaves of in-degree $1$ bijectively labelled by $[n]$, tree vertices of in-degree $1$ and out-degree $2$, and reticulations of in-degree $2$ and out-degree $1$, counted up to isomorphism fixing the leaf labels. It is **tree-child** if every non-leaf vertex has a child that is not a reticulation; such a network has at most $n-1$ reticulations. Let $T_{n,k}$ be the number of tree-child networks with $n$ leaves and $k$ reticulations. The Pons–Batle identity gives the recurrence

$$
T_{n,k}=(n-k+1)\,T_{n,k-1}+\frac{n(2n+k-3)}{n-k}\,T_{n-1,k},\qquad 1\le k<n,
$$

with $T_{n,0}=(2n-3)!!$ and $T_{n,n}=0$. Normalize by the tree-like count,

$$
R_{n,k}=\frac{T_{n,k}}{\binom nk\,(2n+2k-3)!!}.
$$

**Exact coefficient representation.** Define $f_0=1$ and, for $i\ge1$, $f_i$ by $\sum_{j=0}^{i}\frac{\Gamma((3i+j-1)/2)}{j!}f_{i-j}=0$. For $0\le j\le k$ put $H_j(n,k)=k(k-1)\cdots(k-j+1)\,\frac{\Gamma(n+k-(j+1)/2)}{\Gamma(n+k-1/2)}$. Then $R_{n,k}=\sum_{j=0}^{k}f_jH_j(n,k)$ for all $0\le k\le n$.

**Theorem (entire Airy scaling function).** Let $\mathcal A=\int_0^1 e(t)\,dt$ be the area under a standard Brownian excursion $e$. The coefficients $f_j$ have the entire generating function

$$
F(z)=\sum_{j\ge0}f_jz^j=e^{-z^2/3}\,\mathbb E\,e^{-\sqrt2\,z\mathcal A}.
$$

For $|\arg z|<3\pi/4$, with the principal power and $a_1>a_2>\cdots$ the (negative) zeros of the Airy function $\operatorname{Ai}$,

$$
F(z)=2\sqrt\pi\,z\,e^{-z^2/3}\sum_{\nu\ge1}e^{a_\nu z^{2/3}},
$$

and $|f_j|\le2\sqrt2\,(5e/(3j))^{j/2}$ for $j\ge1$.

**Theorem (critical expansion).** For every fixed $X<\infty$, uniformly over integers $0\le k\le X\sqrt n$ and with $x=k/\sqrt n$,

$$
R_{n,k}=F(x)-\frac{xF''(x)+x^2F'(x)}{2\sqrt n}+O_X(n^{-1}).
$$

Since $F(x)>0$ for $x\ge0$, this also holds as a relative expansion. In particular $R_{n,k}\to1$ when $k=o(\sqrt n)$: below the square-root scale, almost every way of choosing $k$ reticulations on a tree-like skeleton is tree-child, and at $k=x\sqrt n$ the surviving fraction is the Gaussian-weighted Laplace transform of Brownian excursion area.

## Expansion

Dividing the counting recurrence by $\binom nk(2n+2k-3)!!$ turns it into a harmonic averaging recurrence $R_{n,k}=\frac{kR_{n,k-1}+(2n+k-3)R_{n-1,k}}{2(n+k)-3}$ with $R_{n,0}=1$ and $R_{n,n}=0$. Its solution is a series in the Gamma-ratio basis $H_j$, and the boundary condition $R_{n,n}=0$ forces the Gamma-weighted convolution identity defining $f_j$. The exponential generating identity of that convolution is the moment recursion of the Brownian excursion area (equivalently, of the classical spectral formula for the excursion-area transform), which identifies $F$. Because $H_j(n,k)\approx x^j$ when $k=x\sqrt n$, the series converges to $F(x)$; a second-order expansion of the Gamma ratios gives the $n^{-1/2}$ correction.

## Sources

- Miquel Pons Viver, "Counting tree-child and reticulation visible networks", arXiv (2026), Section 2: Proposition 2.1, Theorem 2.2 and Theorem 2.3, <https://doi.org/10.48550/arXiv.2611.32460>
