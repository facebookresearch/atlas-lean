# Linear-time likelihood and posterior FDR control for somatic variant calls

**Model.** At a candidate variant locus let $\theta_h$ and $\theta_c$ be the allele frequencies of the variant among healthy and cancer genome copies, $\beta \in \{0, \tfrac12, 1\}$ the strand bias ($\beta = \tfrac12$: no bias), and $\alpha \in (0, 1]$ the tumour purity. The healthy sample yields read pairs $Z^h_1, \dots, Z^h_k$ and the tumour sample $Z^t_1, \dots, Z^t_l$. Each read pair $Z_i$ has latent indicators $\omega_i \sim \mathrm{Bernoulli}(\pi_i)$ (correctly mapped, with $\pi_i$ from the mapping quality) and $\xi_i$ (carries the variant), with $\xi_i \sim \mathrm{Bernoulli}(\theta\tau_i)$ in a pure sample, where $\tau_i$ is the probability that a fragment from a variant-carrying copy covers the variant. Let $p_i$, $a_i$, $o_i$ be the likelihoods of the read data if it supports the variant, supports the reference, or is mismapped (computed once by a pair hidden Markov model), and $s_i$ the strand likelihood. A somatic tumour variant is the event $\theta_h = 0 < \theta_c$.

**Factorization.** Given $(\theta_h, \theta_c, \beta)$ the read pairs are conditionally independent and

$$L(\theta_h, \theta_c, \beta \mid Z^h, Z^t) = \prod_{i=1}^{k} P(Z^h_i \mid \theta_h, \beta) \prod_{j=1}^{l} P(Z^t_j \mid \theta_h, \theta_c, \beta),$$

where each factor is a sum over the three latent cases (mismapped; mapped and reference; mapped and variant). For a healthy read,

$$P(Z^h_i \mid \theta_h, \beta) = \pi_i \bigl[\theta_h \tau_i\, p_i s_i + (1 - \theta_h \tau_i)\, \bar a_i\bigr] + (1 - \pi_i)\, \bar o_i,$$

with $\bar a_i, \bar o_i$ the reference and mismapping likelihoods including a strand factor; for a tumour read the mapped part is the mixture with weights $\alpha$ (cancer copy, frequency $\theta_c$) and $1 - \alpha$ (healthy copy, frequency $\theta_h$).

**Theorem 1 (linear time).** $L(\theta_h, \theta_c, \beta \mid Z^h, Z^t)$ can be evaluated in $O(k + l)$ arithmetic operations at any parameter value, so posterior probabilities of events (somatic tumour, somatic healthy, germline, absent) can be obtained by numerical quadrature over $(\theta_h, \theta_c)$.

**Theorem 2 (concavity).** Fix $\theta_h, \beta$. Suppose the healthy-sample likelihood is positive, the set $\{\theta_c \in [0,1] : P(Z^t_j \mid \theta_h, \theta_c, \beta) > 0 \ \forall j\}$ is a non-empty interval, $\alpha > 0$, and some tumour read has $\pi_j > 0$ and $p_j \ne a_j$. Then $\theta_c \mapsto \log L(\theta_h, \theta_c, \beta \mid Z^h, Z^t)$ is concave on $[0,1]$ and the likelihood has a unique global maximizer $\hat\theta_c$, used as the cancer allele-frequency estimate (with $\theta_h = 0$, $\beta = \tfrac12$).

**FDR control.** If $p_i$ is the posterior probability that call $i$ is a somatic tumour variant, the expected false discovery rate of a call set $C$ is

$$\mathrm{FDR}(C) = \frac{1}{|C|} \sum_{i \in C} (1 - p_i).$$

The largest set with $\mathrm{FDR}(C) \le \gamma$ is obtained by sorting calls by $1 - p_i$ ascending and taking the longest prefix whose running mean stays at most $\gamma$.

## Expansion

Conditional independence of reads given the frequencies gives the product; marginalizing each read's latent pair $(\omega_i, \xi_i)$ by Chapman–Kolmogorov leaves three terms, so each factor costs $O(1)$ once $p_i, a_i, o_i$ are precomputed, which is why the whole likelihood is linear in coverage; a naive treatment of the joint latent configuration would be exponential. In $\theta_c$ each tumour factor is affine, $u_j + v_j \theta_c$ with $v_j \ne 0$ for informative reads, so its logarithm is concave and the sum of logarithms is concave on the region where all factors are positive; the informative-read condition makes it strictly concave, giving uniqueness. The expected-FDR formula is the posterior expectation of the false-discovery proportion; because the running mean of sorted $1 - p_i$ is nondecreasing, the prefix rule yields the maximal set.

## Sources

- J. Köster, L. J. Dijkstra, T. Marschall, A. Schönhuth, "Varlociraptor: enhancing sensitivity and controlling false discovery rate in somatic indel discovery", Genome Biology (2020), "Foundation of the approach" (likelihood Eq. 1, Theorem 1, classification, allele-frequency estimation Eqs. 6–7 and Theorem 2, false discovery rate control) and Methods ("The model", Eqs. 9–14; Theorem 3, Eqs. 37–39; Corollary 1). <https://doi.org/10.1186/s13059-020-01993-6> (PMC7187499).
