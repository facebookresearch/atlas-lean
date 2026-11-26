# CAUSE marginal likelihood as a bivariate normal scale mixture

In the [CAUSE model](cause-summary-statistic-model.md), suppose the per-variant effects $(\beta_{M,j}, \theta_j)$ are independent draws from the mixture

$$p(\beta_{M,j}, \theta_j \mid \Omega) = \sum_{k=0}^K \pi_k\, \mathcal N_2\!\left(\begin{pmatrix}\beta_{M,j}\\ \theta_j\end{pmatrix}; \begin{pmatrix}0\\0\end{pmatrix}, \Sigma_k\right), \qquad \Sigma_k = \begin{pmatrix} \sigma_{k,1}^2 & 0\\ 0 & \sigma_{k,2}^2\end{pmatrix},$$

with pre-specified $\Sigma_k$ and mixing proportions $\pi_k \ge 0$ summing to $1$ ($\Omega = \{\pi_k, \Sigma_k\}$). For $x \in \mathbb R$ let $A(x) = \begin{pmatrix}1 & 0\\ x & 1\end{pmatrix}$. Then the marginal density of the summary statistics is

$$p\big(\hat\beta_{M,j}, \hat\beta_{Y,j} \mid \gamma, \eta, q, \Omega, \rho\big) = q \sum_{k=0}^K \pi_k\, \mathcal N_2\!\big(0,\; A(\gamma+\eta)\Sigma_k A(\gamma+\eta)^{\top} + S_j(\rho)\big) + (1-q)\sum_{k=0}^K \pi_k\, \mathcal N_2\!\big(0,\; A(\gamma)\Sigma_k A(\gamma)^{\top} + S_j(\rho)\big),$$

each density evaluated at $(\hat\beta_{M,j}, \hat\beta_{Y,j})$. Treating variants as independent, the likelihood of all summary statistics is the product of these densities over $j$.

## Depends on

- [CAUSE model of correlated and uncorrelated pleiotropy](cause-summary-statistic-model.md)

## Expansion

Within each component, $(\beta_{M,j}, \beta_{Y,j})^{\top} = A(c)\,(\beta_{M,j}, \theta_j)^{\top}$ with $c = \gamma$ or $c = \gamma + \eta$, so a $\mathcal N_2(0, \Sigma_k)$ draw of $(\beta_{M,j}, \theta_j)$ gives true effects distributed as $\mathcal N_2(0, A(c)\Sigma_k A(c)^\top)$. Adding independent measurement error $\mathcal N_2(0, S_j(\rho))$ adds the covariances. The mixture prior follows the adaptive-shrinkage construction: a flexible unimodal distribution with mode at the origin. CAUSE estimates $\Omega$ and $\rho$ once, then approximates the posterior of $(\gamma, \eta, q)$ on an adaptive grid, using a $\mathrm{Beta}(1, 10)$ prior on $q$ by default.

## Sources

- J. Morrison, N. Knoblauch, J. H. Marcus, M. Stephens, X. He, "Mendelian randomization accounting for correlated and uncorrelated pleiotropic effects using genome-wide summary statistics", Nature Genetics 52 (2020), 740–747, <https://doi.org/10.1038/s41588-020-0631-4> (PMC7343608). Methods, Section 4.1, Equations (2)–(7).
