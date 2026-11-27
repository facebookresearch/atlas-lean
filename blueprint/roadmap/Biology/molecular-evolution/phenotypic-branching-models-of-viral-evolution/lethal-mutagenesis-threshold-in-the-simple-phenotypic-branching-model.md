# Lethal-mutagenesis threshold in the simple phenotypic branching model

**Model.** Viral particles are classified by their replication capacity $r \in \{0,1,\dots,R\}$, where $R$ is the maximal capacity. In each generation a particle of class $r$ produces exactly $r$ progeny. Independently, each copy suffers a deleterious effect with probability $d$, becoming class $r-1$, or a neutral effect with probability $c = 1 - d$, staying in class $r$. Beneficial effects are neglected. Class-$0$ particles leave no progeny. The particle of class $r$ thus has a binomial offspring law $(\mathrm{Bin}(r,d)$ copies of class $r-1$, the rest of class $r)$, and the population $\mathbf Z_n = (Z_n^0,\dots,Z_n^R)$ is a decomposable multitype Galton–Watson process. Its mean matrix is triangular with eigenvalues

$$\lambda_r = r(1-d), \qquad r = 0,\dots,R,$$

so the Malthusian parameter is $m = \varrho(\mathbf M) = R(1-d)$.

**Theorem.**

1. (Three regimes.) Starting with at least one particle of maximal class $R$, the process is subcritical if $R(1-d) < 1$, so the virus goes extinct almost surely in finite time. It is critical if $R(1-d) = 1$, with almost sure extinction. It is supercritical if $R(1-d) > 1$: the virus survives with positive probability and then grows like $m^n$. The extinction threshold in the $(d,R)$ plane is the curve $R = 1/(1-d)$.
2. (Lethal mutagenesis.) The population is driven to extinction exactly when $(1-d)R < 1$: the product of the probability of a neutral replication and the maximal replication capacity must fall below $1$. This is a criterion combining a mutational component ($d$) and an ecological component ($R$).
3. (Stationary class distribution.) In the supercritical case, started with one particle of class $R$, the relative class frequencies converge, up to a random scalar factor, to the binomial distribution

$$u_k = \binom Rk(1-d)^kd^{R-k}, \qquad k = 0,\dots,R .$$

Hence the asymptotic mean replication capacity is $R(1-d)$ and the phenotypic diversity (variance) is $Rd(1-d)$. Starting from a single particle of class $r \in \{2,\dots,R\}$ gives the analogous stationary state with $R$ replaced by $r$. Classes $0$ and $1$ are always subcritical.

## Expansion

Since a class-$r$ particle has $r$ offspring, of which a $\mathrm{Bin}(r, 1-d)$ number stay in class $r$, the mean matrix has $M_{rr} = r(1-d)$ on the diagonal and $M_{r,r-1} = rd$ below it. It is triangular, so its eigenvalues are the diagonal entries. The top class $R$ alone is a single-type Galton–Watson process with mean $R(1-d)$, which decides survival. Lower classes are fed by it and have strictly smaller growth rates, so they cannot sustain the population on their own. Sevastyanov's classification of decomposable multitype processes gives the regimes. The generalized Kesten–Stigum theorem gives convergence of $\mathbf Z_n/m^n$ to $W\mathbf u$, with $\mathbf u$ the right eigenvector for $\lambda_R$. Solving the triangular eigen-system yields binomial coefficients, because each copy independently keeps its class with probability $1-d$.

## Sources

- Fernando Antoneli, Francisco Bosco, Diogo Castro, Luiz Mario Janini, "Viral Evolution and Adaptation as a Multivariate Branching Process", in *BIOMAT 2012* (2013), 217–243, <https://doi.org/10.1142/9789814520829_0013>; preprint arXiv:1110.3368, <https://doi.org/10.48550/arXiv.1110.3368>. Numbering of the arXiv version: Section "Phenotypic Models for Viral Evolution" (model, offspring law, mean matrix), Section "The Simple Phenotypic Model" (eigenvalues; Theorem 3.1, three regimes; Corollary 3.1, lethal mutagenesis; Theorem 3.2, stationary state).
