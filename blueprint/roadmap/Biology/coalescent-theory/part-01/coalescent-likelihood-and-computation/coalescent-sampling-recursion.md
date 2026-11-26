# The Griffiths–Tavaré sampling recursion

In the $K$-allele model with mutation matrix $\Gamma = (\gamma_{ij})$, mutation rate $\theta/2$ per lineage and coalescent genealogy, let $q(\mathbf n)$ be the probability that a sample of $n$ genes has type configuration $\mathbf n = (n_1, \dots, n_K)$, and let $\mathbf e_i$ be the unit vectors. For $n \ge 2$, conditioning on the first event back in time (a mutation with probability $\theta/(n + \theta - 1)$, a coalescence otherwise) gives

$$q(\mathbf n) = \frac{\theta}{n + \theta - 1}\Bigl[\sum_{i=1}^K \frac{n_i}{n}\gamma_{ii}\,q(\mathbf n) + \sum_{i \ne j,\ n_j > 0}\frac{n_i + 1}{n}\gamma_{ij}\,q(\mathbf n + \mathbf e_i - \mathbf e_j)\Bigr] + \frac{n - 1}{n + \theta - 1}\sum_{j:\ n_j > 0}\frac{n_j - 1}{n - 1}\,q(\mathbf n - \mathbf e_j),$$

with boundary conditions $q(\mathbf e_i) = \pi_i^*$, the probability that the most recent common ancestor has type $i$ (Tavaré 2004, Theorem 9.1, eqs. (9.3.1)–(9.3.2)). The recursion is on the sample size: given all $q(\mathbf m)$ with $|\mathbf m| < n$, the linear equations for the $q(\mathbf m)$ with $|\mathbf m| = n$ are non-singular. The infinite-alleles analogue is the recursion for the Ewens sampling formula (Tavaré 2004, Sec. 3.5).

## Expansion

1. The $K$-allele model on a coalescent genealogy and the first-event probabilities $\theta/(n + \theta - 1)$ and $(n - 1)/(n + \theta - 1)$.
2. The configurations that lead to $\mathbf n$ after a mutation or a coalescence, and the coefficients above.
3. The boundary conditions and the non-singularity of each level's linear system, hence uniqueness of the solution.
4. The infinite-alleles recursion and the [Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md).
5. Monte Carlo solution of the recursion as an importance sampler, as a separate statement.

## Sources

- Original result: R. C. Griffiths and S. Tavaré, Ancestral inference in population genetics, Statist. Sci. 9 (1994), 307–319. <https://doi.org/10.1214/ss/1177010378> The recursion follows Tavaré (2004), Theorem 9.1.
- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188.
