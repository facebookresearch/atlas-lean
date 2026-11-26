# Spectral consistency of quadratic spatial pattern tests

**Statistic.** Expression values $x_1,\dots,x_n$ are measured at locations $s_1,\dots,s_n$ in a spatial domain $\mathcal S\subseteq\mathbb R^d$. With $\mathbf z=(\mathbf x-\bar x\mathbf 1)/\hat\sigma$ and a symmetric spatial kernel $k$,

$$Q_n=\mathbf z^\top\mathbf K\mathbf z,\qquad K_{ij}=k(s_i,s_j).$$

Under spatial independence $X\perp S$ the values are exchangeable given the locations and $Q_n$ has a weighted chi-square null law set by the spectrum of the centered kernel matrix.

**Population statistic (Theorem 1).** For a bounded continuous characteristic kernel on $\mathcal S$ and the linear kernel $l(x,x')=xx'$ on a scalar $X$ with $0<\mathrm{Var}X<\infty$, let $Q(P_{SX})=\mathrm{HSIC}(P_{SX})=\|C_{SX}\|^2_{\rm HS}$. Then

$$Q(P_{SX})=0\iff \mathbb E[X\mid S]=\mathbb E[X]\ \text{a.s.}$$

So the upper-tail $Q$-test is consistent against every alternative whose conditional mean varies in space, but not against alternatives that preserve the mean (for example a pure change in variance), whatever kernel is used.

**Spectral criterion (Theorem 2).** Let $\mathcal T=\mathcal C\mathcal K\mathcal C$ be the centered integral operator of $k$ on $L^2(P_S)$, where $\mathcal C$ removes the mean; then $Q_n/n^2\to\langle\bar f,\mathcal K\bar f\rangle$ for $x_i=f(S_i)$. With critical values $c_{n,\alpha}/n\to c_\alpha\in(0,\infty)$, the test is consistent against every fixed alternative with nonconstant conditional mean iff $\mathcal T$ is strictly positive definite on mean-zero functions $L^2_0(P_S)$.

**Cancellation.** If the centered kernel matrix is indefinite or singular on $\mathbf 1^\perp$, some nonzero centered pattern $\mathbf f$ has $\mathbf f^\top\widetilde{\mathbf K}\mathbf f=0$, and scaling that pattern up makes $Q_n\to0$: arbitrarily strong patterns can be invisible. Moran's I, whose spectrum gives opposite signs to low- and high-frequency modes, is an example.

## Expansion

Writing a pattern in the eigenbasis of $\mathcal T$, $f=\sum_i\hat f_i\phi_i$, gives $Q(f)=\sum_i\lambda_i\hat f_i^2$: zero eigenvalues are blind spots and mixed signs allow exact cancellation, while a strictly positive spectrum weighs every mode positively. The linear data kernel makes HSIC see only $\mathbb E[X\mid S]$, so variance patterns need a different data kernel. This frequency view also defines a bivariate statistic $R=\mathbf z_x^\top\mathbf K\mathbf z_y$ for comparing patterns, which is a kernel inner product when the spectral weights are nonnegative.

## Sources

- J. Su, J. H. Fung, H. Wang, D. Yang, "Consistent and scalable detection and comparison of spatial patterns", arXiv:2602.02825 (2026), Methods (quadratic statistic), Theorem 1 and its corollaries, Theorem 2 and its corollary, Propositions B.1, C.1 and C.2, <https://doi.org/10.48550/arXiv.2602.02825>.
