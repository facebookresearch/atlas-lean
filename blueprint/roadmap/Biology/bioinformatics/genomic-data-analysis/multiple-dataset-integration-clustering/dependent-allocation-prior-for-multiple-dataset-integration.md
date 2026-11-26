# Dependent allocation prior for multiple dataset integration

**Setting.** Genes $i = 1, \dots, n$ are observed in $K$ datasets, $x_{ik}$ being the measurement of gene $i$ in dataset $k$. Each dataset is a finite Dirichlet-multinomial allocation (DMA) mixture with the same number $N$ of components:

$$x_{ik} \mid c_{ik}, \theta \sim F(\theta_{c_{ik} k}), \qquad \theta_{ck} \sim G^{(0)}_k, \qquad \pi_{\cdot k} = (\pi_{1k}, \dots, \pi_{Nk}) \sim \mathrm{Dirichlet}(\alpha_k/N, \dots, \alpha_k/N),$$

where $F$ may differ between datasets (Gaussian process, multinomial, bag-of-words) and $c_{ik} \in \{1, \dots, N\}$ is the component allocation. Multiple Dataset Integration (MDI) couples the allocations of each gene through the conditional prior

$$p(c_{i1}, \dots, c_{iK} \mid \pi, \Phi) \;\propto\; \prod_{k=1}^K \pi_{c_{ik} k} \prod_{k=1}^{K-1}\prod_{l=k+1}^K \bigl(1 + \phi_{kl}\, \mathbf{1}[c_{ik} = c_{il}]\bigr),$$

independently over genes, with association parameters $\phi_{kl} \ge 0$ for the $K(K-1)/2$ dataset pairs. Component $c$ in dataset $k$ is identified with component $c$ in dataset $l$.

**Proposition.**

1. If all $\phi_{kl} = 0$, the allocations are independent across datasets and the model is $K$ independent DMA mixtures.
2. For $K = 2$, with $s = \sum_{c=1}^N \pi_{c1}\pi_{c2}$ (the chance of agreement under independence), the normalizing constant is $1 + \phi_{12}\, s$ and

$$\Pr(c_{i1} = c_{i2} \mid \pi, \phi_{12}) = \frac{(1 + \phi_{12})\, s}{1 + \phi_{12}\, s}.$$

This is non-decreasing in $\phi_{12}$, equals $s$ at $\phi_{12} = 0$, and tends to $1$ as $\phi_{12} \to \infty$ when $s > 0$. Each agreeing configuration has its prior weight multiplied by $1 + \phi_{12}$ relative to the independent case.
3. (Fusion probabilities) For a subset $S \subseteq \{1, \dots, K\}$ the posterior fusion probability of gene $i$ across $S$ is $\Pr(c_{ik} \text{ equal for all } k \in S \mid x)$, estimated by the fraction of posterior Gibbs samples in which the allocations agree; gene $i$ is called *fused* across $S$ when this probability exceeds $1/2$.

## Expansion

(1) is immediate because every coupling factor is $1$. (2): summing the unnormalized prior over $(c_1, c_2)$ gives $\sum_{c, c'} \pi_{c1}\pi_{c'2} + \phi_{12}\sum_c \pi_{c1}\pi_{c2} = 1 + \phi_{12} s$; the agreeing configurations carry weight $(1 + \phi_{12}) s$. The derivative of $(1 + \phi)s/(1 + \phi s)$ in $\phi$ has the sign of $s(1 - s) \ge 0$. Because components are matched by index across datasets, a finite $N$ is used rather than a Dirichlet process; $N$ is only an upper bound on the number of occupied clusters, which is inferred separately for each dataset. Inference is by Gibbs sampling over allocations, mixture weights, component parameters and the $\phi_{kl}$; fused genes are then grouped into a single clustering by maximizing the posterior expected adjusted Rand index among sampled partitions. The posterior of $\phi_{kl}$ measures how similar the clustering structures of datasets $k$ and $l$ are.

## Sources

- P. Kirk, J. E. Griffin, R. S. Savage, Z. Ghahramani, D. L. Wild, "Bayesian correlated clustering to integrate multiple datasets", Bioinformatics 28 (2012) 3290–3297, Sections 2.1–2.4, Eqs. (1)–(3), <https://doi.org/10.1093/bioinformatics/bts595> (PMC3519452).
