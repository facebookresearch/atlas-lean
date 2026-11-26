# Phase-aware likelihood ratio for fetal trisomy and its sensitivity index

Let $L$ heterozygous maternal sites along a chromosome have phased allele counts $(a_i, b_i)$ in maternal plasma, with $a_i$ the count of the homolog-I allele and $n_i = a_i + b_i$. For a sequence of inheritance states $X = (x_1, \dots, x_L)$ define

$$\mathcal{L}(X \mid A, B, f, c, s) = \prod_{i=1}^{L} P\big(a_i \mid n_i, \pi(x_i), \rho\big) \prod_{i=2}^{L} \tau(x_{i-1}, x_i),$$

where $P(k \mid n, \pi, \rho)$ is the beta-binomial probability with mean fraction $\pi$ and intraclass correlation $\rho$, $\pi(x)$ is the expected plasma allelic fraction of state $x$ at fetal fraction $f$, and the transition weights for assumed numbers $c$ of crossovers and $s$ of phasing switch errors are

$$\tau(x, x) = 1, \quad \tau(H_1, H_2) = \frac{c + s}{L}, \quad \tau(H_{11}, H_{22}) = \frac{s}{L}, \quad \tau(H_{11}, H_{12}) = \tau(H_{12}, H_{22}) = \frac{c}{L}$$

(symmetrically in the two arguments). With $\Omega_3$ and $\Omega_2$ the state sequences over the trisomic states $\{H_{11}, H_{12}, H_{22}\}$ and the euploid states $\{H_1, H_2\}$, the **log-likelihood-ratio discrimination statistic** is

$$\mathrm{LLR} = \log_{10} \frac{\max_{X \in \Omega_3} \mathcal{L}(X \mid A, B, f, c, s)}{\max_{X \in \Omega_2} \mathcal{L}(X \mid A, B, f, c, s)},$$

each maximum being computed by the Viterbi algorithm in time linear in $L$. If the LLR has mean $\mu_3, \mu_2$ and variance $\sigma_3^2, \sigma_2^2$ under trisomic and euploid fetuses, its **sensitivity index** is

$$d' = \frac{\mu_3 - \mu_2}{\sqrt{(\sigma_3^2 + \sigma_2^2)/2}},$$

and when the two LLR distributions are normal with equal variances, the area under the ROC curve of the test that thresholds the LLR satisfies $\mathrm{AUC} = \Phi(d'/\sqrt2)$, i.e. $d' = \sqrt2\,\Phi^{-1}(\mathrm{AUC})$.

## Depends on

- [Expected maternal-plasma allelic fraction under fetal inheritance states](expected-plasma-allelic-fraction-under-fetal-inheritance-states.md): the expected fractions $\pi(x)$
- [Beta-binomial mass function](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/beta-binomial/beta-binomial-pmf.md): the site emission probabilities $P(a_i \mid n_i, \pi, \rho)$
- [Viterbi computes the MAP value of a chain CRF](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/conditional-random-fields/sup-viterbi-eq.md): each maximum over state sequences is computed by the Viterbi recursion
- [Standard normal CDF](../../../../Probability/central-limit-theorems/berry-esseen-theorem/kolmogorov-distance/normal-cdf.md): $\Phi$ in the AUC identity

## Proof depends on

- [Concatenation of independent Gaussian random vectors](../../../../Probability/distributions/continuous/gaussian-conditioning/map-sum-equiv-prod-symm-of-indep-fun.md): $(Z_3, Z_2)$ is jointly Gaussian
- [Linear images of multivariate Gaussians](../../../../Probability/distributions/continuous/gaussian-conditioning/map-to-euclidean-lin-multivariate-gaussi.md): $Z_3 - Z_2$ is Gaussian with variance $2\sigma^2$

## Expansion

The model is a hidden Markov model whose hidden state is the maternal inheritance state; the transition weights act as penalties that let the signal be integrated over long runs of consecutive sites while allowing a limited number of recombination and phasing-error changes. Phase gives every site a predicted direction of deviation, so an SPH segment of $k$ sites accumulates evidence coherently instead of being diluted among the opposite-direction sites, which is why phasing lowers the fetal fraction at which trisomy is detectable. The beta-binomial overdispersion matters: with a plain binomial model, extra-binomial noise is fitted by SPH segments and inflates the LLR. For the AUC identity, with $Z_3 \sim \mathcal N(\mu_3, \sigma^2)$ and $Z_2 \sim \mathcal N(\mu_2, \sigma^2)$ independent, $\mathrm{AUC} = \Pr(Z_3 > Z_2) = \Phi\big((\mu_3 - \mu_2)/(\sigma\sqrt2)\big)$.

## Sources

- G. Genovese, C. J. Mello, P.-R. Loh, R. E. Handsaker, S. Kashin, C. W. Whelan, L. A. Bayer-Zwirello and S. A. McCarroll, "Chromosomal phase improves aneuploidy detection in non-invasive prenatal testing at low fetal DNA fractions", *Scientific Reports* 12 (2022), 12025, Methods "NIPT simulation" and Fig. 2, <https://doi.org/10.1038/s41598-022-14049-5> (PMC9283487).
