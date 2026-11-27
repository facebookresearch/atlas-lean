# Bayes factor for differential expression from a variational posterior

Let $\rho^g(z, s) = f_w^g(z, s)$ be the normalized expression frequency of gene $g$ predicted by the fitted [scVI generative model](zero-inflated-negative-binomial-likelihood-of-the-scvi-generative-model.md) for latent state $z$ and batch $s$, and let $p(s)$ be the relative abundance of batch $s$. For two cells $a, b$ with observed counts $x_a, x_b$, let $S$ be a batch drawn from $p$ independently of the latent states, and define the mutually exclusive hypotheses

$$H_1^g : \rho^g(z_a, S) > \rho^g(z_b, S), \qquad H_2^g : \rho^g(z_a, S) \le \rho^g(z_b, S),$$

in which the two cells are compared within one common random batch, and the log posterior odds

$$K^g = \log \frac{p(H_1^g \mid x_a, x_b)}{p(H_2^g \mid x_a, x_b)}.$$

Approximating the posterior of the latent states by the variational distributions $q(z_a \mid x_a)\, q(z_b \mid x_b)$ gives

$$p(H_1^g \mid x_a, x_b) \approx \sum_s p(s) \Pr_{z_a \sim q(\cdot \mid x_a),\ z_b \sim q(\cdot \mid x_b)}\big[\rho^g(z_a, s) > \rho^g(z_b, s)\big], \qquad p(H_2^g \mid x_a, x_b) = 1 - p(H_1^g \mid x_a, x_b),$$

with equality for the variational law, and the low-dimensional integrals are estimated by naive Monte Carlo, which is consistent by the law of large numbers. Under equal prior odds $K^g$ is the log Bayes factor. Its sign indicates the more probable hypothesis; $|K^g| > 3$ (odds of about $e^3 \approx 20$) is taken as strong evidence. To compare two subpopulations, $K^g$ is averaged over many randomly drawn cell pairs, one from each subpopulation, assuming cells are independent and identically distributed within each.

**A different estimand.** The source writes its hypotheses with the batch average inside the comparison, $\mathbb{E}_s\, \rho^g(z_a, s) > \mathbb{E}_s\, \rho^g(z_b, s)$, while computing the displayed sum, which is the probability of $H_1^g$ above. The two events differ: for two equally frequent batches and fixed latent states with differences $\rho^g(z_a, s) - \rho^g(z_b, s)$ equal to $+0.4$ and $-0.2$, the batch-averaged comparison holds with probability $1$, while $H_1^g$ has probability $1/2$. More Monte Carlo samples do not remove this difference; the displayed procedure is the source's operational statistic, and it estimates $H_1^g$ as defined here.

## Depends on

- [Zero-inflated negative binomial likelihood of the scVI generative model](zero-inflated-negative-binomial-likelihood-of-the-scvi-generative-model.md)

## Remarks

Because the hypotheses are defined through $\rho^g$, which is already conditioned on the batch and freed of library size, the test controls for nuisance factors by construction rather than by calibrating all data to one batch, and it favours genes that differ consistently across batches. Calibration is checked by running the procedure on two halves of one cluster, where no gene should cross the threshold. The test is a posterior-probability statement, not a frequentist $p$-value: no multiple-testing correction is built in, and its validity rests on the variational posterior being an adequate surrogate for the true posterior.

## Sources

- R. Lopez, J. Regier, M. B. Cole, M. I. Jordan and N. Yosef, "Deep generative modeling for single-cell transcriptomics", Nature Methods 15 (2018), 1053–1058, Online Methods (section "Bayesian differential expression"), <https://doi.org/10.1038/s41592-018-0229-2>, PMCID: PMC6289068.
