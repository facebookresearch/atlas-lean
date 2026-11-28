# ρ confidence set of causal variants

Let $\mathcal M$ be a set of $m$ SNPs with observed association statistics $\hat s \in \mathbb R^m$ and a likelihood $\mathbb P(\hat s \mid c)$ for causal configurations $c \in \mathcal C = \{-1, 0, 1\}^m$, such as the [multivariate normal model](multivariate-normal-model-of-ld-correlated-association-statistics.md). Put a prior under which SNPs are causal independently, each with probability $\gamma$ in each direction:

$$\mathbb P(c) = \prod_{i=1}^m \gamma^{|c_i|} (1 - 2\gamma)^{1 - |c_i|}, \qquad \mathbb P(c \mid \hat s) = \frac{\mathbb P(\hat s \mid c)\, \mathbb P(c)}{\sum_{c' \in \mathcal C} \mathbb P(\hat s \mid c')\, \mathbb P(c')}. \tag{2}$$

For $K \subseteq \mathcal M$ let $\mathcal C_K$ be the configurations whose causal SNPs all lie in $K$ (including the null configuration $c = 0$). The *confidence level* of $K$ is

$$\rho(K) = \mathbb P(\mathcal C_K \mid \hat s) = \sum_{c \in \mathcal C_K} \mathbb P(c \mid \hat s),$$

the posterior probability that $K$ captures every causal SNP, and $K$ is a *$\rho$ confidence set* when $\rho(K) \ge \rho$. Given a threshold $\rho^*$, the fine-mapping target is a $\rho^*$ confidence set of minimum size.

**Properties.** $\rho$ is monotone, $K \subseteq K' \Rightarrow \rho(K) \le \rho(K')$, and $\rho(\mathcal M) = 1$, so a minimum-size $\rho^*$ confidence set exists for every $\rho^* \in [0, 1]$. When the prior and likelihood allow at most one causal SNP, $\rho(K) = \mathbb P(0 \mid \hat s) + \sum_{i \in K} \mathrm{PIP}_i$ and a minimum set is obtained by sorting SNPs by posterior inclusion probability, as for [credible sets](is-credible-set.md); with several causal SNPs, $\rho$ is not additive over SNPs and a SNP can be needed only jointly with another.

In practice the number of causal SNPs per configuration is capped (at most six in the source, giving $\sum_{i \le 6} 2^i \binom m i$ configurations) and the set is grown greedily, adding at each step the SNP that most increases $\rho(K)$.

## Depends on

- [Multivariate normal model of LD-correlated association statistics](multivariate-normal-model-of-ld-correlated-association-statistics.md)
- [Credible set of variants](is-credible-set.md)

## Expansion

Monotonicity holds because $\mathcal C_K \subseteq \mathcal C_{K'}$. Under a single-causal model the configurations in $\mathcal C_K$ are the null and the single-SNP configurations with $i \in K$ (both signs), so $\rho(K)$ is the null posterior plus the sum of the PIPs over $K$, and the prefix argument for credible sets applies.

## Sources

- F. Hormozdiari, E. Kostem, E. Y. Kang, B. Pasaniuc and E. Eskin, *Identifying causal variants at loci with multiple signals of association*, Genetics 198 (2014), 497–508, <https://doi.org/10.1534/genetics.114.167908>, PMCID PMC4196608 (Materials and Methods: posterior probability of causal SNP statuses, equation (2); Optimization).
