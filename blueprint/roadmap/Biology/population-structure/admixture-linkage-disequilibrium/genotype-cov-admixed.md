# Diploid genotype covariance in an admixed population

For all real numbers $\alpha, p_A, q_A, p_B, q_B, r$ and every natural number $n$ (Loh et al. 2013, Eq. 3),

$$z\bigl(R_r^n(x)\bigr) = 2 \alpha (1 - \alpha) (1 - r)^n\, (p_A - p_B)(q_A - q_B),$$

where $z$ is the [genotype covariance](genotype-cov.md), $x$ the [pulse gamete frequencies](source-mix.md) and $R_r^n$ the $n$-fold random-mating recursion with recombination fraction $r$ (see [decay of admixture LD](linkage-diseq-admixed.md)). For $0 \le \alpha \le 1$, allele frequencies in $[0, 1]$ and $0 \le r \le 1$, the factor $(1 - r)^n$ is the exact discrete-generation decay.

## Sources

- P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger, *Inferring admixture histories of human populations using linkage disequilibrium*, Genetics 193 (2013), 1233–1254, Eq. 3.
