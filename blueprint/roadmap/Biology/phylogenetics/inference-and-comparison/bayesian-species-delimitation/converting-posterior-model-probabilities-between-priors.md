# Converting posterior model probabilities between priors

Let models $i = 1, \dots, m$ have marginal likelihoods $L_i > 0$, obtained by integrating the likelihood over all model parameters (and, for multilocus data, averaging over the gene trees). Under a prior $\pi$ with $\pi_i > 0$ the posterior probabilities are

$$\mathbb{P}_i = \frac{\pi_i L_i}{\sum_{k=1}^m \pi_k L_k}.$$

If $\pi'$ is a second prior with $\pi'_i > 0$, then for every pair of models

$$\frac{\mathbb{P}'_i}{\mathbb{P}'_j} = \frac{\pi'_i}{\pi'_j} \cdot \frac{L_i}{L_j} = \frac{\pi'_i}{\pi'_j} \cdot \frac{\pi_j}{\pi_i} \cdot \frac{\mathbb{P}_i}{\mathbb{P}_j},$$

so the posterior under $\pi'$ is recovered from the posterior under $\pi$ by $\mathbb{P}'_i \propto (\pi'_i / \pi_i) \mathbb{P}_i$, normalized to sum to one. The ratio $L_i / L_j$ is the Bayes factor of model $i$ against model $j$ and does not depend on the prior.

## Depends on

- [Bayes' rule for countably many hypotheses](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/bayes-posterior-apply-singleton.md)

## Expansion

The identity is Bayes' theorem written for odds: posterior odds equal prior odds times the Bayes factor, and dividing out one set of prior odds and multiplying in another changes nothing else. In species delimitation the number of models grows super-exponentially with the number of populations, and different reasonable priors (uniform over models, uniform over delimitations, or the proportional priors) induce very different prior probabilities for the number of species, so the reweighting is the practical way to report how strongly a delimitation conclusion depends on the prior. It is exact when the posterior probabilities are known exactly; with Monte Carlo estimates, models that are rare under $\pi$ but favoured under $\pi'$ inherit large relative error. The reweighting changes model probabilities only; if the parameter priors (for example on $\theta$) change, the marginal likelihoods $L_i$ change too, and the posterior must be recomputed.

## Sources

- Yang Z, Rannala B. Unguided species delimitation using DNA sequence data from multiple loci. *Molecular Biology and Evolution* 31:3125–3135 (2014), Discussion, equations (1) and (2). DOI <https://doi.org/10.1093/molbev/msu279>. PMCID PMC4245825.
