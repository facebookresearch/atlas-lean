# Negative binomial and Gaussian limits of the equilibrium protein number

Consider the three-stage gene expression model with a constitutively active gene ($k_- = 0$): mRNAs are produced at rate $k_M$ and degraded at rate $\gamma_M$, each mRNA produces proteins at rate $k_P$, and proteins are degraded at rate $\gamma_P$. Let $P$ be the equilibrium protein number.

1. **Negative binomial limit (short-lived mRNAs).** Fix $a > 0$ and let $\gamma_M \to \infty$ with $k_P/\gamma_M = a$. Then $P$ converges in distribution to $N(a)$ with

    $$\mathbb{P}(N(a) = n) = \frac{\Gamma(\kappa + n)}{n!\,\Gamma(\kappa)}\Bigl(\frac{1}{1+a}\Bigr)^{\kappa}\Bigl(\frac{a}{1+a}\Bigr)^{n}, \qquad n \in \mathbb{N},\quad \kappa = \frac{k_M}{\gamma_P},$$

    the negative binomial law with generating function $\mathbb{E}(z^{N(a)}) = (1 + a - a z)^{-\kappa}$.

2. **Gaussian limit (long-lived proteins).** As $\gamma_P \to 0$ with the other parameters fixed,

    $$\frac{P - \mathbb{E}(P)}{\sqrt{\mathbb{E}(P)}} \Longrightarrow \mathcal{N}\bigl(0, \sigma^2\bigr), \qquad \sigma^2 = 1 + \frac{k_P}{\gamma_M}.$$

With exponential protein lifetimes, the gene always active, and general mRNA lifetime and elongation-time distributions, the mRNA lifetime $L_1$ having $\mathbb E(L_1^3) < \infty$, the same scaling still gives a Gaussian limit for $\sqrt{\gamma_P}\,(P - \mathbb{E}(P))$, but the limiting variance then depends on the distribution of protein elongation times.

## Depends on

- [Moments and Fano factors of the three-stage gene expression model](moments-and-fano-factors-of-the-three-stage-gene-expression-model.md)

## Expansion

At equilibrium the protein count is a functional of a marked Poisson process of mRNA births, which gives an explicit generating function for $P$. Each short-lived mRNA emits a geometric burst of proteins with mean $a$, and bursts arrive at rate $k_M$ and decay at rate $\gamma_P$, which produces the negative binomial law. When proteins live long, $P$ sums many weakly dependent bursts, and a Laplace-transform expansion of the Poisson representation gives the Gaussian limit with the burst-inflated variance.

## Sources

- Philippe Robert, "Mathematical models of gene expression", Probability Surveys 16 (2019), 277–332, <https://doi.org/10.1214/19-ps332>; numbering as in arXiv:1905.02578: Section 2 (Propositions 2, 4 and 5) and the central limit theorem of Section 6.
