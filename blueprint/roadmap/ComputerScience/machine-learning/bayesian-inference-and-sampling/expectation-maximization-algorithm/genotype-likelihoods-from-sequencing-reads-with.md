# Genotype likelihoods from sequencing reads

At a biallelic site, let reads $r_1, \dots, r_m \in \{\mathrm{ref}, \mathrm{alt}\}$ be drawn independently given the genotype $g \in \{0, 1, 2\}$ (copies of the alternative
allele), each from a uniformly chosen chromosome and misreported with probability $\varepsilon_i \in [0, 1]$. The **genotype likelihood** is

$$\mathrm{GL}(g) = \prod_{i=1}^m \mathbb P(r_i \mid g), \qquad \mathbb P(r_i = \mathrm{alt} \mid g) = \frac g2 (1 - \varepsilon_i) + \Bigl(1 - \frac g2\Bigr) \varepsilon_i .$$

With Hardy–Weinberg prior $q(p) = ((1 - p)^2, 2p(1 - p), p^2)$, the genotype posterior is $\mathbb P(g \mid r) \propto \mathrm{GL}(g)\, q_g(p)$. Across individuals, the allele
frequency maximizing $\prod_j \sum_g \mathrm{GL}_j(g) q_g(p)$ is computed by expectation–maximization with the genotypes as latent variables, which does not
decrease this likelihood, by [the monotonicity of EM iterates](log-lik-iterate-monotone.md) resting on the [evidence lower bound](elbo-le-log-lik.md), when every term
$\mathrm{GL}_j(g)\, q_g(p)$ is positive, as for $0 < p < 1$ and $0 < \varepsilon_i < 1$. With no reads $\mathrm{GL}$ is constant and the posterior is the
prior; with $\varepsilon_i = 0$, one read of each allele forces $g = 1$.

## Depends on

- [EM iterates have monotone likelihood](log-lik-iterate-monotone.md)
- [The evidence lower bound](elbo-le-log-lik.md)

## Sources

- H. Li, "A statistical framework for SNP calling, mutation discovery, association mapping and population genetical parameter estimation from sequencing data", Bioinformatics 27 (2011), 2987–2993, <https://doi.org/10.1093/bioinformatics/btr509>.
