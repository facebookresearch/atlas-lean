# Hutchinson's randomized trace estimator

Let $A$ be a real $N\times N$ matrix and let $z$ be a random vector in $\mathbb R^N$ with $E[z] = 0$ and $E[zz^\top] = I_N$ (for example, independent standard normal or Rademacher entries).

**Identity.** $E[z^\top A z] = \operatorname{tr}(A)$.

**Estimator.** For independent copies $z_1,\dots,z_B$ of $z$,

$$\widehat{\operatorname{tr}}_B(A) = \frac1B\sum_{b=1}^B z_b^\top A z_b$$

is unbiased for $\operatorname{tr}(A)$. If $A = MM^\top$ for an $N\times M'$ matrix $M$ (with $M'$ the number of columns), then $z_b^\top A z_b = \|M^\top z_b\|_2^2$, and for $A = K^2$ with $K$ symmetric, $z_b^\top K^2 z_b = \|K z_b\|_2^2$; each term costs matrix–vector products only. For standard normal $z$ and symmetric $A$, $\operatorname{Var}(z^\top A z) = 2\operatorname{tr}(A^2)$, so $\operatorname{Var}(\widehat{\operatorname{tr}}_B(A)) = 2\operatorname{tr}(A^2)/B$.

## Proof sketch

$E[z^\top A z] = E[\operatorname{tr}(A zz^\top)] = \operatorname{tr}(A\,E[zz^\top]) = \operatorname{tr}(A)$ by linearity of trace and expectation. For Gaussian $z$ and symmetric $A = Q\Lambda Q^\top$, $z^\top A z = \sum_i \lambda_i u_i^2$ with $u = Q^\top z$ standard normal, whose variance is $\sum_i 2\lambda_i^2 = 2\operatorname{tr}(A^2)$. In heritability estimation the needed trace is $\operatorname{tr}(K^2)$ for a genetic relationship matrix $K = XX^\top/M$, which costs $O(N^2M)$ to form explicitly but only $O(NMB)$ through $\|X(X^\top z_b)\|^2/M^2$.

## Sources

- M. F. Hutchinson, "A stochastic estimator of the trace of the influence matrix for Laplacian smoothing splines", Communications in Statistics – Simulation and Computation 18 (1989), 1059–1076, <https://doi.org/10.1080/03610918908812806>.
- Y. Wu and S. Sankararaman, "A scalable estimator of SNP heritability for biobank-scale data", Bioinformatics (2018), Sections 2.1–2.4, Equations 1–11, <https://doi.org/10.1093/bioinformatics/bty253> (PMC6022682).
