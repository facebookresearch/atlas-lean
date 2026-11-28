# DATES ancestry covariance for dating admixture

Let an admixed genome $C$ descend from sources $A$ and $B$ with proportions $\alpha$ and $\beta = 1 - \alpha$ through a single pulse $t$ generations ago. At each marker $i$ let $g_i$ be the genotype of $C$, and let $a_i = P(g_i \mid A)$ and $b_i = P(g_i \mid B)$ be the probabilities of $g_i$ given the reference allele frequencies of $A$ and $B$ (the mixture fraction $\alpha$ is first fitted by least squares, minimizing $\sum_i \bigl(g_i - \alpha p_{A,i} - (1 - \alpha) p_{B,i}\bigr)^2$). The single-marker likelihood is $L_i = \alpha a_i + \beta b_i$. For two markers $d$ Morgans apart, with probability $\theta = e^{-td}$ of no recombination since the pulse, the pair log-likelihood is

$$\mathcal{L} = \log\Bigl[(1 - \theta) L_1 L_2 + \theta\,(\alpha a_1 a_2 + \beta b_1 b_2)\Bigr].$$

**Proposition.** The coefficient of $\theta$ in the expansion of $\mathcal{L}$ about $\theta = 0$ is $Q\,K_1 K_2$, where

$$Q = \alpha\beta, \qquad K_i = \frac{a_i - b_i}{L_i}.$$

The **ancestry covariance** at distance $d$ is the empirical covariance of these per-marker scores over the set $S(d)$ of marker pairs at distance $d$,

$$A(d) = \frac{1}{|S(d)|} \sum_{(S_1, S_2) \in S(d)} (K_1 - \bar K_1)(K_2 - \bar K_2),$$

summed over individuals when several genomes are available. Under a single pulse, $A(d)$ decays exponentially, $A(d) \propto e^{-(t + 1) d}$, and the admixture time is estimated by a least-squares fit of an exponential with an affine term to $A(d)$. The method works from one diploid genome and needs no phasing.

## Depends on

- [Local-ancestry covariance in Morgans](allele-cov-ancestry-pulse-haldane.md)
- [Expected ALDER weighted linkage disequilibrium](weighted-ld.md)

## Expansion

By the chain rule, $\partial_\theta \mathcal{L}\big|_{\theta = 0} = \dfrac{\alpha a_1 a_2 + \beta b_1 b_2 - L_1 L_2}{L_1 L_2}$, and

$$\alpha a_1 a_2 + \beta b_1 b_2 - (\alpha a_1 + \beta b_1)(\alpha a_2 + \beta b_2) = \alpha(1 - \alpha) a_1 a_2 + \beta(1 - \beta) b_1 b_2 - \alpha\beta(a_1 b_2 + b_1 a_2) = \alpha\beta (a_1 - b_1)(a_2 - b_2),$$

using $1 - \alpha = \beta$; dividing by $L_1 L_2$ gives $\alpha\beta K_1 K_2$. Thus $K_i$ is a per-marker ancestry score, and the covariance of scores at distance $d$ inherits the decay of the covariance of local-ancestry labels. The exponent $t + 1$ reflects that the first admixed generation carries one intact chromosome from each source, so ancestry starts to break up only in the next meiosis; ALDER and ROLLOFF fit $t$ instead, which matters only for very recent admixture. The FFT implementation computes $A(d)$ for all distance bins in near-linear time, as for ALDER's weighted linkage disequilibrium.

## Sources

- M. Chintalapati, N. Patterson and P. Moorjani, "The spatiotemporal patterns of major human admixture events during the European Holocene", eLife (2022), e77625, Materials and methods, "DATES: model and implementation" (Eqs. (1)–(4)) and Appendix 1, <https://doi.org/10.7554/eLife.77625>, PMCID PMC9293011.
