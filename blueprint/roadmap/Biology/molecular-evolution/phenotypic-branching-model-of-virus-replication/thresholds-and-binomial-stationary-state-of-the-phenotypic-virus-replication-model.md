# Thresholds and binomial stationary state of the phenotypic virus-replication model

**Model.** Viral particles replicate in discrete, non-overlapping generations and are classified by their mean replication capacity $r \in \{0, 1, \dots, R\}$, where $R$ is the maximal capacity. A particle of class $r$ produces a random number of copies with law $t_r$ of mean $r$ ($t_0 = \delta_0$). Each copy independently suffers a deleterious effect (class $r-1$) with probability $d$, a neutral effect (class $r$) with probability $c$, or a beneficial effect (class $\min(r+1, R)$) with probability $b$, where $b + c + d = 1$. This is a multitype Galton–Watson process whose mean matrix depends on the $t_r$ only through their means. In the **simple phenotypic model** $b = 0$, so $c = 1 - d$, and the mean matrix is bidiagonal: a class-$r$ particle has on average $rc$ offspring in class $r$ and $rd$ in class $r-1$. Its Malthusian parameter (Perron root) is

$$m = R(1-d).$$

**Theorem.** In the simple phenotypic model, started from at least one particle of class $R$:

1. if $m < 1$ the population becomes extinct in finite time almost surely (subcritical);
2. if $m > 1$ the population survives with positive probability and then grows like $m^n$ in generation $n$ (supercritical);
3. if $m = 1$ the population becomes extinct almost surely, possibly after a very long time (critical).

In the supercritical case the class composition converges: up to a random scalar factor, the numbers of particles in classes $k = 0, \dots, R$ become proportional to the binomial distribution

$$\pi_k = \binom{R}{k}(1-d)^k d^{R-k}, \qquad k = 0, \dots, R.$$

**Corollary (lethal mutagenesis).** Since $e^{-U_d} = 1 - d$ is the fraction of offspring without non-neutral changes and $R_{\max} = R$, the extinction criterion $e^{-U_d}R_{\max} < 1$ of lethal mutagenesis is exactly the subcritical condition $m < 1$.

## Expansion

The mean matrix $M$ is triangular, so its eigenvalues are the diagonal entries $rc$, $r = 0, \dots, R$, and the Perron root is $Rc = R(1-d)$, attained by the top class. The extinction/survival trichotomy follows from multitype Galton–Watson theory (the process is reducible, so one uses the decomposition into the single-type top class and the classes it feeds). The binomial vector is a left eigenvector for $Rc$: $\pi_j\,jc + \pi_{j+1}(j+1)d = Rc\,\pi_j$ because $\binom{R}{j+1}(j+1) = \binom{R}{j}(R-j)$. Limit theorems for supercritical multitype branching processes then give convergence of $Z_n/m^n$ to a random multiple of $\pi$, nonzero on survival. Spectral perturbation theory extends these thresholds to small beneficial probability $b > 0$.

## Sources

- Fernando Antoneli, Francisco Bosco, Diogo Castro, Luiz Mario Janini, "Virus Replication as a Phenotypic Version of Polynucleotide Evolution", arXiv (2012). Section 2 (phenotypic model), Section 3 (mean matrix, Theorems 1, 2 and 3), Appendix A (spectral perturbation). <https://doi.org/10.48550/arXiv.1204.6353>
