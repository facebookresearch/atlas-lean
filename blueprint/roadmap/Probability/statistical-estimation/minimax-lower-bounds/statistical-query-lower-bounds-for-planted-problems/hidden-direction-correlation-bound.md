# Hidden-direction distributions matching m moments have tiny pairwise correlations

Let $A$ be a distribution on $\mathbb{R}$ whose first $m$ moments agree with those of $\mathcal{N}(0,1)$ and with $\chi^2(A, \mathcal{N}(0,1)) < \infty$. For a unit vector $v \in \mathbb{R}^n$ let $P_v$ be the distribution on $\mathbb{R}^n$ that is $A$ in direction $v$ and standard Gaussian in the orthogonal complement. Then for unit vectors $u, v$,

$$
\big|\chi_{\mathcal{N}(0,I_n)}(P_u, P_v)\big| \le |\langle u, v\rangle|^{m+1}\,\chi^2\big(A, \mathcal{N}(0,1)\big).
$$

## Proof sketch

Expand the density ratio $\frac{dA}{d\mathcal{N}}$ in normalized Hermite polynomials $h_k$; moment matching kills the coefficients for $1 \le k \le m$. The correlation of $P_u$ and $P_v$ under the Gaussian equals $\sum_{k \ge m+1}\langle u,v\rangle^k a_k^2$ with $a_k = \mathbb{E}_A[h_k]$, by the Mehler-type identity $\mathbb{E}[h_k(\langle u, g\rangle)h_j(\langle v, g\rangle)] = \delta_{jk}\langle u,v\rangle^k$, and $\sum_k a_k^2 = \chi^2(A, \mathcal{N})$.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Sources

- I. Diakonikolas, D. M. Kane, A. Stewart, "Statistical Query Lower Bounds for Robust Estimation of High-Dimensional Gaussians and Gaussian Mixtures", FOCS (2017), arXiv:1611.03473.
