# Dirichlet-multinomial law of prestige-biased role-model choice

**Model.** A generation has $N$ role-models with trait values $A_1,\dots,A_N$ and $N$ copiers who choose a role-model one at a time. Let $K_{i,j}$ be the number of the first $i$ copiers who chose role-model $j$ ($K_{0,j}=0$). Copier $i$ chooses $j$ with probability

$$G_{i,j}=\frac{\alpha\,\beta(A_j+e)+(1-\alpha)K_{i-1,j}}{\alpha\sum_{k=1}^N\beta(A_k+e)+(1-\alpha)(i-1)},$$

where $\beta>0$ is a success-bias function (e.g. $\beta(a)=b\exp(-(a-\hat A)^2/2J)$), $e$ is the copier's estimation error, taken equal for all copiers, and $\alpha\in(0,1)$ weights success bias against prestige bias (the number of copiers a role-model already has). Each copier then adopts the trait of its chosen role-model.

**Corollary 3.1 (expected number of copiers).** For every $j$,

$$\mathbb E[K_{N,j}]=N\,G_{1,j}=N\,\frac{\beta(A_j+e)}{\sum_k\beta(A_k+e)}=\frac{\beta(A_j+e)}{\overline{\beta(A+e)}},$$

so prestige bias does not change the expected share of each role-model, only the variability around it.

**Corollary 3.2 (Dirichlet-multinomial law).** The vector of copier counts is Dirichlet-multinomial,

$$K_N\sim\mathrm{DirMult}\big(N;\ \theta_1,\dots,\theta_N\big),\qquad \theta_j=\frac{\alpha}{1-\alpha}\,\beta(A_j+e),$$

with mean $N\,\theta_j/\theta_0$ and variance $N\frac{\theta_j}{\theta_0}\big(1-\frac{\theta_j}{\theta_0}\big)\frac{N+\theta_0}{1+\theta_0}$, where $\theta_0=\sum_k\theta_k$. As $\alpha\to1$ (pure success bias) this tends to the multinomial law of independent choices; as $\alpha\to0$ (pure prestige bias) the overdispersion factor grows and a few role-models capture most copiers.

## Depends on

- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Proof depends on

- [Pólya urn predictive law is invariant under reordering](../../../../Probability/bayesian-statistics/blackwell-macqueen-urn/polya-urn-predictive-comp-perm.md)

## Expansion

Dividing numerator and denominator of $G_{i,j}$ by $1-\alpha$ shows that the choice process is a Pólya urn: role-model $j$ starts with weight $\theta_j$ and gains one unit of weight each time it is chosen. A Pólya urn with initial weights $\theta$ run for $N$ draws produces counts with the Dirichlet-multinomial law with parameter $\theta$, equivalently a multinomial sample from shares drawn from $\mathrm{Dirichlet}(\theta)$. The paper derives the same law as an approximation when estimation errors vary between copiers, and validates it numerically for $N=100$. Iterating over generations yields a Wright-Fisher-like cultural dynamic whose effective drift is inflated by prestige bias.

## Sources

- Egozi S, Ram Y, "Prestige bias in cultural evolutionary dynamics", R Soc Open Sci 2024 Jul 10;11(7):230650, Equations (2.6)-(2.11) and Corollaries 3.1-3.2, <https://doi.org/10.1098/rsos.230650>, PMCID PMC11285825.
