# Consistent-group hierarchical model for isoform proportions across RNA-seq samples

**Model.** Consider a gene with $J$ annotated isoforms and $D$ RNA-seq samples, sample $d$ contributing reads $\mathbf{R}^{(d)} = \{r^{(d)}_1, \dots, r^{(d)}_{n_d}\}$, each summarized by the exons hit by its two ends and its genomic positions. The latent isoform of origin of read $i$ in sample $d$ is $Z^{(d)}_i \in \{1, \dots, J\}$, with $\mathbb{P}(Z^{(d)}_i = j) = \tau^{(d)}_j$, and given its origin each read has an isoform-specific generative likelihood (position and fragment-length model). A latent indicator $E_d \in \{0,1\}$ marks whether sample $d$ belongs to the **consistent group** of samples representing the tissue of interest:

$$
\boldsymbol\tau^{(d)} = E_d\,\boldsymbol\alpha + (1 - E_d)\,\boldsymbol\beta^{(d)},
$$

so all consistent samples share the isoform proportions $\boldsymbol\alpha$, the target parameter, while every other sample has its own $\boldsymbol\beta^{(d)}$. The priors are $E_d \mid \gamma \sim \mathrm{Bernoulli}(\gamma)$ independently, $\gamma \sim \mathrm{Beta}(a, b)$, and Dirichlet priors with parameter $\boldsymbol\lambda$ on $\boldsymbol\alpha$ and the $\boldsymbol\beta^{(d)}$.

**Gibbs sampler.** Integrating out $\boldsymbol\alpha$ and $\boldsymbol\beta^{(d)}$ (Dirichlet-multinomial conjugacy), the full conditionals are

- $\gamma \mid \cdot \sim \mathrm{Beta}\big(\sum_d E_d + a,\ D - \sum_d E_d + b\big)$;
- $Z^{(d)}_i \mid \cdot$, a categorical distribution proportional to the joint probability of the data with $Z^{(d)}_i = j$;
- $E_d \mid \cdot$, Bernoulli with odds equal to $\gamma/(1-\gamma)$ times ratios of Dirichlet-multinomial marginal likelihoods of the pooled consistent-group reads and of sample $d$ alone.

At iteration $t$ the consistent-group proportions are estimated by pooling reads from the samples with $E^{(t)}_d = 1$,

$$
\alpha^{(t)}_j = \frac{\lambda_j + \sum_{d}E^{(t)}_d\sum_{i=1}^{n_d}\mathbf{1}\{Z^{(d,t)}_i = j\}}{\sum_{j'}\lambda_{j'} + \sum_d E^{(t)}_d\, n_d}, \qquad \hat{\boldsymbol\alpha}^{\mathrm{MSIQ}} = \frac1T\sum_{t=1}^T\boldsymbol\alpha^{(t)} .
$$

**Lemma (consistency of the estimator).** As the number $T$ of post-burn-in Gibbs iterations grows,

$$
\lim_{T\to\infty}\hat{\boldsymbol\alpha}^{\mathrm{MSIQ}} = \mathbb{E}\big(\boldsymbol\alpha\mid\mathbf{R}, \boldsymbol\lambda, a, b\big).
$$

## Expansion

$\alpha^{(t)}_j$ is the conditional posterior mean $\mathbb{E}(\alpha_j \mid \mathbf{Z}^{(t)}, \mathbf{E}^{(t)}, \mathbf{R})$ under the Dirichlet prior, so averaging it over the chain is a Rao-Blackwellized Monte Carlo estimate. By the ergodic theorem for the Gibbs chain and the tower property it converges to the marginal posterior mean of $\boldsymbol\alpha$. Pooling only the consistent samples, rather than all samples with equal weight, protects the estimate from contaminated or off-target libraries. Samples are effectively weighted by their posterior probability $\mathbb{P}(E_d = 1\mid\mathbf{R})$ of sharing the dominant read distribution. In simulations and real data this reduced isoform quantification error relative to single-sample or naive pooling methods.

## Depends on

- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Proof depends on

- [Dirichlet–multinomial conjugacy](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/posterior-categorical-seq-kernel-dirichl.md)

## Sources

- Wei Vivian Li, Anqi Zhao, Shihua Zhang and Jingyi Jessica Li, "MSIQ: Joint Modeling of Multiple RNA-seq Samples for Accurate Isoform Quantification", arXiv (2016), Section 2 (parameters, data summary, hidden states and priors, Gibbs sampling, estimator and Lemma 2.1), <https://doi.org/10.48550/arXiv.1603.05915>.
