# Effective sample size multiplier for families of equally related members

Consider $N$ individuals arranged in families of $s \ge 2$ members, where every pair within a family has relatedness $r \in [0, 1)$ and members of different families are unrelated, so the kinship matrix is block diagonal with blocks $K_s = (1 - r) I_s + r J_s$ ($J_s$ the all-ones matrix). Let the trait covariance be $\Sigma_y = \sigma_a^2 K + \sigma_r^2 I$ and the genotype covariance $\Sigma_w = K$. Then the trace approximation of the LMM effective sample size multiplier is

$$\gamma_\beta = \frac{1}{s}\left(\frac{rs + 1 - r}{(rs + 1 - r)\,\sigma_a^2 + \sigma_r^2} + \frac{(s - 1)(1 - r)}{(1 - r)\,\sigma_a^2 + \sigma_r^2}\right).$$

For sibling pairs ($s = 2$, $r = 1/2$) this reads $\gamma_\beta = \tfrac12\left(\frac{3/2}{\tfrac32\sigma_a^2 + \sigma_r^2} + \frac{1/2}{\tfrac12\sigma_a^2 + \sigma_r^2}\right)$.

## Depends on

- [Effective sample size multiplier of a mixed-model association test](ess-multiplier-of-a-mixed-model-association-test.md): its trace approximation

## Expansion

The block $K_s$ has eigenvalue $1 + (s - 1) r = rs + 1 - r$ on the all-ones vector and eigenvalue $1 - r$ with multiplicity $s - 1$ on its orthogonal complement. Substituting into $\gamma_\beta \approx N^{-1} \sum_i \lambda_i / (\sigma_a^2 \lambda_i + \sigma_r^2)$, every family contributes the same sum, and dividing by its size $s$ gives the formula. As a check, $r = 0$ gives $\gamma_\beta = 1/(\sigma_a^2 + \sigma_r^2)$, which is $1$ for a standardized trait, so unrelated individuals gain nothing. The formula lets a study designer compare, before genotyping, the power of family-based and unrelated designs as a function of family size, relatedness and heritability.

## Sources

- A. Ziyatdinov, J. Kim, D. Prokopenko, F. Privé, F. Laporte, P.-R. Loh, P. Kraft and H. Aschard, "Estimating the effective sample size in association studies of quantitative traits", *G3: Genes, Genomes, Genetics* (2021), jkab057, Results Eqs. (28) and (31), <https://doi.org/10.1093/g3journal/jkab057> (PMC8495748).
