# Gene-tree density on a species network and integration over population sizes

Let $\Psi$ be a time-calibrated species network with branches $b = 1, \dots, B$ and reticulation nodes $h = 1, \dots, H$, reticulation $h$ carrying inheritance probability $\gamma_h \in [0, 1]$. Branch $b$ has effective population size $N_b > 0$, shared by all loci. For loci $j = 1, \dots, L$ with ploidy $p_j > 0$ (for example $2$ for autosomal and $1/2$ for mitochondrial genes in diploids), let the gene tree $G_j$ (with coalescent times) be embedded in $\Psi$, and record for each branch $b$: the number $n_{jb}$ of lineages entering at its tipward end, the number $k_{jb}$ of coalescences inside it, and the lengths $c_{jbi}$ ($0 \le i \le k_{jb}$) of the $k_{jb} + 1$ intervals between successive events; and for each reticulation $h$ the numbers $u_{jh}$ and $v_{jh}$ of lineages that take the $\gamma_h$ parent and the $1 - \gamma_h$ parent.

**Density.** Under the multispecies network coalescent with time in calendar units,

$$f(G \mid \Psi, \gamma, N) = \prod_{j=1}^{L} \left[\prod_{b=1}^{B} (p_j N_b)^{-k_{jb}} \exp\!\left(-\frac{1}{p_j N_b} \sum_{i=0}^{k_{jb}} c_{jbi} \binom{n_{jb} - i}{2}\right) \prod_{h=1}^{H} \gamma_h^{u_{jh}} (1 - \gamma_h)^{v_{jh}}\right] = \Lambda \prod_{b=1}^{B} r_b\, N_b^{-q_b} \exp\!\left(-\frac{\sigma_b}{N_b}\right),$$

with $q_b = \sum_j k_{jb}$, $r_b = \prod_j p_j^{-k_{jb}}$, $\sigma_b = \sum_j p_j^{-1} \sum_i c_{jbi} \binom{n_{jb} - i}{2}$ and $\Lambda = \prod_j \prod_h \gamma_h^{u_{jh}} (1 - \gamma_h)^{v_{jh}}$. When $\Psi$ has no reticulation, $\Lambda = 1$ and this is the multispecies coalescent density on a species tree.

**Theorem (analytic integration over population sizes).** If the $N_b$ are independent with inverse-gamma$(\alpha, \beta)$ priors, density $\beta^\alpha \Gamma(\alpha)^{-1} N^{-\alpha - 1} e^{-\beta / N}$, then

$$f(G \mid \Psi, \gamma) = \int f(G \mid \Psi, \gamma, N)\, f(N \mid \alpha, \beta)\, dN = \Lambda \prod_{b=1}^{B} \frac{r_b\, \beta^{\alpha}\, \Gamma(\alpha + q_b)}{(\beta + \sigma_b)^{\alpha + q_b}\, \Gamma(\alpha)},$$

and the posterior of each $N_b$ given the gene trees is inverse-gamma$(\alpha + q_b, \beta + \sigma_b)$.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../../../coalescent-theory/multispecies-coalescent/network-multispecies-coalescent-fixed-network-ge.md)

## Proof depends on

- [Euler's gamma integral](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/lintegral-rpow-mul-exp-neg-mul-ioi.md)

## Expansion

Within a branch, while $m$ lineages remain each pair coalesces at rate $1/(p_j N_b)$, so an interval of length $c$ with $m$ lineages contributes the survival factor $\exp(-\binom{m}{2} c/(p_j N_b))$ and each coalescence contributes the rate $1/(p_j N_b)$; after $i$ coalescences $m = n_{jb} - i$. Each lineage crossing a reticulation independently picks a parent with probabilities $\gamma_h$, $1 - \gamma_h$, giving $\Lambda$. Collecting powers of $N_b$ across loci yields an unnormalized inverse-gamma kernel in each $N_b$, and $\int_0^\infty N^{-(\alpha + q) - 1} e^{-(\beta + \sigma)/N}\, dN = \Gamma(\alpha + q) (\beta + \sigma)^{-(\alpha + q)}$ gives the closed form. Removing the $B$ population-size parameters from the state space simplifies reversible-jump MCMC over networks, gene trees and embeddings; sequence data enter through the product of per-locus phylogenetic likelihoods given the gene trees.

## Sources

- C. Zhang, H. A. Ogilvie, A. J. Drummond and T. Stadler, "Bayesian inference of species networks from multilocus sequence data", Molecular Biology and Evolution 35 (2018), Eqs. (2)–(3), <https://doi.org/10.1093/molbev/msx307> (PMC5850812).
