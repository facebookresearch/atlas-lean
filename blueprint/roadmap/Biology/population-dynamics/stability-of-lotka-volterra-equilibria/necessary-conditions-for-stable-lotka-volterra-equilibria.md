# Necessary conditions for stable Lotka-Volterra equilibria

**Setting.** The $n$-species Lotka-Volterra system is
$$x_i'=r_ix_i\Bigl(1-\frac1{K_i}\sum_{j=1}^n\alpha_{ij}x_j\Bigr),\qquad i=1,\dots,n,$$
on $\mathbb R^n_{\ge0}$, with growth rates $r_i>0$, carrying capacities $K_i>0$ and interaction matrix $A=(\alpha_{ij})$. An equilibrium $x^*$ in the closed orthant is *feasible* if all $x_i^*>0$ and *sub-feasible of order $k$* if exactly $k$ coordinates ($0<k<n$) vanish, on an index set $I$; generic position of the nullcline hyperplanes $\sum_j\alpha_{ij}x_j=K_i$ is assumed. Let $D^*=\mathrm{diag}\bigl((r_1/K_1)x_1^*,\dots,(r_n/K_n)x_n^*\bigr)$ and $B=D^*A$. For a square matrix $M$, $\mathcal D_k(M)$ denotes the set of its $k\times k$ principal submatrices (with the empty minor equal to $1$). $F_i(x)=r_i(1-K_i^{-1}\sum_j\alpha_{ij}x_j)$ is the per-capita growth rate.

**Earlier sufficient conditions (Theorems 2.1-2.3).** If $A$ is Volterra-Lyapunov (diagonally) stable, i.e. there is a positive diagonal $W$ with $WA+A^{\mathsf T}W$ positive definite, then the system has a unique stable equilibrium and $A$ is a $P$-matrix. If all off-diagonal $\alpha_{ij}\le0$ (mutualism), an equilibrium in the orthant is stable if and only if $A$ is a $P$-matrix.

**Theorem 3.1 (necessary conditions).** If a feasible equilibrium is stable, then
$$\sum_{C\in\mathcal D_k(B)}\det C>0\qquad\text{for every }k=0,1,\dots,n .$$
If a sub-feasible equilibrium with zero set $I$ is stable, then $F_i(x^*)<0$ for every $i\in I$ (no absent species can invade) and the analogous principal-minor sums of the matrix $D^*A$ restricted to the surviving species are positive in every order.

**Proposition 4.1.** If $|\alpha_{ij}|<1$ for all $i\ne j$ (with the normalization above, so that $\alpha_{ii}=1$), there is always at least one stable equilibrium.

## Expansion

At a feasible equilibrium the Jacobian is $J=-D^*A=-B$, so its characteristic polynomial is $\det(\lambda I+B)=\sum_{k=0}^n\bigl(\sum_{C\in\mathcal D_k(B)}\det C\bigr)\lambda^{n-k}$. Local asymptotic stability requires all roots of this polynomial in the open left half-plane, and a real polynomial with all roots there (a Hurwitz polynomial) has all coefficients of the same sign, which gives the minor-sum conditions. At a sub-feasible equilibrium the Jacobian is block triangular: the absent species contribute the eigenvalues $F_i(x^*)$, which must be negative, and the surviving species contribute $-D^*A$ on their indices. The conditions are weaker than the $P$-matrix condition (each individual principal minor positive), which is sufficient in the mutualistic case but not necessary in general.

## Sources

- M. Aspenberg, E. Martens, K. Wollein Waldetoft, "Stable equilibria in the Lotka-Volterra equations", arXiv preprint (2025), Theorems 2.1-2.3, Theorem 3.1, Proposition 4.1, <https://doi.org/10.48550/arXiv.2512.13347>.
