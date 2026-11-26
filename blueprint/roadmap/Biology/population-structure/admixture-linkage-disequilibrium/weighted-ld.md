# Expected ALDER weighted linkage disequilibrium

Let $\mu$ be a measure on a measurable space $\Omega$ and let $p_X : \Omega \to \mathbb{R}$ be the allele frequency of each population $X$. For real numbers $\alpha, r$, a natural number $n$ and populations $A, B, R, S$, the weighted LD integral is

$$W = \int z\bigl(R_r^n(x^{\omega})\bigr)\, \bigl(p_R(\omega_1) - p_S(\omega_1)\bigr)\bigl(p_R(\omega_2) - p_S(\omega_2)\bigr) \, d(\mu \otimes \mu)(\omega_1, \omega_2),$$

where $x^{\omega}$ are the [pulse gamete frequencies](source-mix.md) with parameters $\alpha$, $p_A(\omega_1)$, $p_A(\omega_2)$, $p_B(\omega_1)$, $p_B(\omega_2)$, $R_r^n$ is the $n$-fold random-mating recursion and $z$ the [genotype covariance](genotype-cov.md), with the convention that the integral of a non-integrable function is $0$. When $\mu$ is a probability measure, $0 \le \alpha \le 1$, $0 \le r \le 1$ and the frequencies lie in $[0, 1]$, the two loci are independent draws $\omega_1, \omega_2$ from $\mu$ and this is the expected weighted LD, the ALDER two-site statistic $\mathbb{E}[z(x, y)\, w(x)\, w(y)]$ with weights $w = p_R - p_S$ (Loh et al. 2013, Appendix A).

## Sources

- P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger, *Inferring admixture histories of human populations using linkage disequilibrium*, Genetics 193 (2013), 1233–1254, Appendix A.
