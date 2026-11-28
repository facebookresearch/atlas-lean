# Fixed points of truncated-product multivalued networks

**Setting.** On $X_m=\{0,\tfrac1m,\dots,1\}$ with Łukasiewicz operations $\neg x=1-x$ and $x\odot y=\max\{0,x+y-1\}$, a $\odot$-$\neg$ network is a map $F=(f_1,\dots,f_n):X_m^n\to X_m^n$ whose coordinates are truncated products $f_i=\bigodot_{j\in A_i}x_j^{p_{ij}}\odot\bigodot_{j\in B_i}\neg(x_j)^{q_{ij}}\odot\frac{c_i}m$ with $A_i\cap B_i=\emptyset$. Steady states are fixed points $F(x)=x$.

**Theorem 32 (max-linear form).** Every nonzero coordinate function can be written uniquely as $f_i(x)=\max\{0,\ell_i(x)\}$ with

$$\ell_i(x)=\sum_{j\in A_i}p_{ij}x_j-\sum_{j\in B_i}q_{ij}x_j+\frac{c_i}m-\sum_{j\in A_i}p_{ij},$$

where $p_{ij},q_{ij}\in\{1,\dots,c_i\}$.

**Corollary 37.** Let $L'\in\mathbb Z^{n\times n}$ be the matrix of coefficients of the linear parts $\ell'_i(x)=\sum_{A_i}p_{ij}x_j-\sum_{B_i}q_{ij}x_j$. If $\det(L'-I_n)\ne0$, there is at most one fixed point with all coordinates nonzero. More generally (Theorem 36), for each set $I$ of coordinates whose functions contain a $\odot$ operation, invertibility of the corresponding matrix $M_I$ (diagonal entries $\ell_{ii}-1$, off-diagonal $\ell_{ij}$) gives at most one fixed point in the region $\mathcal R_I$ attached to $I$.

**Proposition 28 (structural zeros).** If the wiring diagram contains two directed paths from the same node $x_j$ to $x_k$, both consisting of activating edges except for a single inhibitory edge leaving $x_j$, then $x_k=0$ at every steady state.

**Proposition 13 (generic fixed points).** With $q=(m+1)^n$, the fraction of all maps $X_m^n\to X_m^n$ having at least one fixed point is $1-\big(\tfrac{q-1}q\big)^q$, which tends to $1-1/e\approx0.632$ as $n\to\infty$ or $m\to\infty$.

## Depends on

- [Łukasiewicz normal form of multivalued network functions](lukasiewicz-normal-form-of-multivalued-network-functions.md)

## Expansion

Since $\bigodot_{k=1}^ra_k=\max\{0,\sum a_k-(r-1)\}$, expanding the canonical form gives the max-linear expression directly. On the region where the coordinates in a set are positive, the fixed-point equations become the linear system $x_i=\ell_i(x)$ there and $x_i=0$ elsewhere, so a nonsingular coefficient matrix allows at most one solution per region, and fixed points are found by solving one linear system per sign pattern instead of enumerating $(m+1)^n$ states. Proposition 28 is a graph-level reduction: along the two paths the same upstream value $x_j$ reaches $x_k$ once directly and once negated, and in a truncated product a literal and its negation cannot both be large, so the product vanishes at steady state. Proposition 13 counts maps with no fixed point: each of the $q$ states avoids itself in $q-1$ ways.

## Sources

- J. García Galofre, M. Pérez Millán, A. Galarza Rial, R. Laubenbacher, "Beyond Boolean networks: new tools for the steady state analysis of multivalued networks", *SIAM Journal on Applied Dynamical Systems* 25(1) (2026), 77–107, Proposition 13, Proposition 28, Theorem 32, Theorem 36 and Corollary 37, <https://doi.org/10.1137/24m1657249> (preprint arXiv:2404.16760).
