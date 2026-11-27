# Modified outcomes and outcome-weighted learning for epistasis

Let $X \in \{0,1,2\}^p$ be a genotype, $A \in \{-1, +1\}$ a binarized target SNP, and $Y$ a phenotype ($Y \in \{0, 1\}$ for case–control). Decompose

$$\mu(X) = \tfrac12\big[\mathbb E(Y \mid A = +1, X) + \mathbb E(Y \mid A = -1, X)\big], \qquad \delta(X) = \tfrac12\big[\mathbb E(Y \mid A = +1, X) - \mathbb E(Y \mid A = -1, X)\big],$$

and write $\delta(X) = \delta_0 + \delta_1(X)$ with $\mathbb E\,\delta_1(X) = 0$: $\delta_0$ is the main effect of $A$ and the SNPs in the support of $\delta_1$ are those in epistasis with $A$. Let $\tilde A = (A+1)/2$ and let $e(X) = \mathbb P(\tilde A = 1 \mid X)$ be the **propensity score**, which is not constant because of linkage disequilibrium.

**Modified outcome identity.** With

$$\tilde Y = Y\Big(\frac{\tilde A}{e(X)} - \frac{1 - \tilde A}{1 - e(X)}\Big),$$

one has $\delta(X) = \tfrac12\,\mathbb E[\tilde Y \mid X]$, so the support of $\delta$ can be estimated by sparse regression of $\tilde Y$ on $X$, without modelling $\mu$.

**Lemma (outcome-weighted learning).** For a non-increasing loss with the logistic form $\phi(u) = \log(1 + e^{-u})$, any minimizer

$$d^* \in \arg\min_{d : \{0,1,2\}^p \to \mathbb R}\ \mathbb E\Big[\frac{Y}{\mathbb P(A \mid X)}\,\phi\big(A\,d(X)\big)\Big]$$

satisfies $d^*(x) = \ln\dfrac{\mathbb E[Y \mid A = +1, X = x]}{\mathbb E[Y \mid A = -1, X = x]}$; hence $d^*$ has the same sign as $\delta$ everywhere, and estimating it is a logistic regression of $A$ on $X$ with sample weights $W = Y/\mathbb P(A \mid X)$.

## Depends on

- [Propensity score](../../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/propensity.md)

## Proof depends on

- [Identification of the average treatment effect by inverse probability weighting](../../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/integral-ipw-ate.md)

## Expansion

The identity follows from $\mathbb E[Y\tilde A \mid X] = \mathbb E[Y \mid X, \tilde A = 1]\,e(X)$ and $\mathbb E[Y(1 - \tilde A) \mid X] = \mathbb E[Y \mid X, \tilde A = 0]\,(1 - e(X))$; it generalizes the case $e \equiv 1/2$ of independent $A$ and $X$. For the lemma, conditionally on $X = x$ the objective is $\phi(u)\,\mathbb E[Y \mid A = 1, x] + \phi(-u)\,\mathbb E[Y \mid A = -1, x]$, whose stationarity condition with the logistic loss gives $e^{u}$ equal to the ratio. With $Y \in \{0,1\}$, controls get weight zero, giving a case-only analysis whose dependence between $A$ and $X$ is handled by the weights rather than an independence assumption. Propensity scores come from a haplotype hidden Markov model on the target's chromosome after removing SNPs in tight LD with the target; shifted, normalized or robust inverse-propensity weights stabilize the estimators, and the support is chosen by elastic net with stability selection.

## Sources

- L. Slim, C. Chatelain, C.-A. Azencott, J.-P. Vert, "Novel methods for epistasis detection in genome-wide association studies", PLoS ONE 15(11) (2020) e0242927, Eqs. (2)–(6) and Lemma 1, <https://doi.org/10.1371/journal.pone.0242927>, PMCID PMC7703915.
