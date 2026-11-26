# Gibbs scaling of ladder distances under the nearest neighbor thermodynamic model

**Setting.** A plane tree is a rooted ordered tree; $\mathfrak{T}_n$ is the set of plane trees with $n$ edges (so $|\mathfrak{T}_n|$ is the Catalan number $C_n$). In the plane tree model of RNA secondary structure, edges are helices and vertices are loops. For a tree $T$ call a non-root vertex a *leaf* if it has no children and *unary* if it has exactly one child; let $d_0(T)$, $d_1(T)$ and $r(T)$ be the numbers of leaves, unary vertices and the root degree. For real parameters $\alpha,\beta,\gamma$ the nearest neighbor thermodynamic model (NNTM) energy is

$$E(T)=\alpha\, d_0(T)+\beta\, d_1(T)+\gamma\, r(T),$$

and $T$ is drawn from $\mathfrak{T}_n$ with Gibbs probability $e^{-E(T)}/Z_{n,\alpha,\beta,\gamma}$. Write $\mathfrak{T}^h_n$ for the same model conditioned on root degree at most $h\in\mathbb{N}$.

The *total contact distance* (path length) $\mathcal{P}^{PL}(T)$ is the sum over vertices of their edge distance to the root, and the *total ladder distance* (Wiener index) $\mathcal{P}^{WI}(T)$ is the sum of edge distances over all unordered vertex pairs. Let $e(t)$ be a normalized Brownian excursion on $[0,1]$ and

$$\rho=e^{-\alpha}+e^{-\beta}+2e^{-\alpha/2},\qquad c(\alpha,\beta)=\frac{\sqrt{\rho}}{(e^{-\alpha/2}+1)\,e^{-\alpha/4}}.$$

**Theorem.** For all $\alpha,\beta,\gamma\in\mathbb{R}$ and every $h\in\mathbb{N}$, as $n\to\infty$ the Gibbs-random tree on $\mathfrak{T}^h_n$ (and on $\mathfrak{T}_n$ with $\gamma=0$) satisfies

$$\frac{\mathcal{P}^{PL}}{\sqrt{2n^3}}\ \xrightarrow{d}\ c(\alpha,\beta)\int_0^1 e(t)\,dt,\qquad \frac{\mathcal{P}^{WI}}{\sqrt{2n^5}}\ \xrightarrow{d}\ c(\alpha,\beta)\iint_{0<s<t<1}\Big(e(s)+e(t)-2\min_{s\le u\le t}e(u)\Big)\,ds\,dt.$$

So the energy parameters only rescale the uniform-tree limits by the explicit constant $c(\alpha,\beta)$ (equal to $1$ at $\alpha=\beta=0$); the path length limit is Airy distributed. More generally, for any subtree additive property $\mathcal{P}^f(T)=\sum_{v\ne\mathrm{root}} f(T_v,T)$ with $f$ a polynomial in the edge, leaf and unary counts of the fringe subtree $T_v$ and of $T$ (with homogeneous top-degree monomials), $\mathcal{P}^f/n^{V'(f)}$ under the Gibbs law has the same limit as $Q(f,\alpha,\beta)\,\mathcal{P}^f/n^{V'(f)}$ under the uniform law, for an explicit constant $Q(f,\alpha,\beta)$ and exponent $V'(f)$ fixed by the degree of $f$.

## Expansion

The proof is a method of moments. The weighted $k$-th moment sums $M_{k,n}(f,\alpha,\beta,\gamma)=\sum_{T\in\mathfrak{T}_n}\mathcal{P}^f(T)^k e^{-E(T)}$ are encoded in generating functions that decompose over a skeleton tree spanning the $k$ marked vertices. Their dominant singularity sits at $x=1/\rho$, with leading term $W(\alpha,\beta,f)(1-\rho x)^{-V_k(f)}$, and the constant factors as a part depending on $(\alpha,\beta)$ only through the top-degree leaf and unary counts times a part independent of the energy. Transfer theorems give the asymptotic moments, the ratio to the uniform case is $Q(f,\alpha,\beta)^k$, and Carleman's condition makes the moments determine the limit law. Restricting root degree to $\le h$ multiplies numerator and normalizer by the same constant, which is why $\gamma$ and $h$ drop out. Taking $f=t+1$ gives path length and $f=(t+1)(n-t)$ gives the Wiener index; the uniform limits are Takács' Airy law and Janson's Wiener index limit.

## Sources

- Anna Kirkpatrick, Chidozie Onyeze, "On the Asymptotic Distributions of Classes of Subtree Additive Properties of Plane Trees under the Nearest Neighbor Thermodynamic Model", arXiv:2101.04714 (2021): Section "The Distribution of Classes of Subtree Additive Properties under NNTM" (main theorems on the moment generating functions, the Gibbs-to-uniform translation theorem and the path length and Wiener index corollaries); energy model and subtree additive properties in "Plane Trees and their Properties". <https://doi.org/10.48550/arXiv.2101.04714>
