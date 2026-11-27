# The fixation-conditioned diffusion does not depend on the sign of genic selection

In a population of effective size $N_e$ with additive selection coefficient $s$, the allele frequency evolves by the diffusion with infinitesimal variance $x(1 - x)/(2N_e)$ and drift $sx(1 - x)$ per generation. Zhao, Lascoux, Overall and Waxman (2013) show that conditioning on eventual fixation, a Doob $h$-transform with $h$ the fixation probability $P_{fix}(x) = (1 - e^{-4N_esx})/(1 - e^{-4N_es})$ for $s \ne 0$, adds to the drift the term $s_{fict}(x)x(1 - x)$ with

$$s_{fict}(x) = s\bigl[\coth(2N_esx) - 1\bigr] \qquad (s \ne 0)$$

(their equations (5)–(8) and Appendix A). For $s = 0$ the fixation probability is $P_{fix}(x) = x$ and the conditioned drift is $\frac{x(1 - x)}{2N_e}\cdot\frac1x = \frac{1 - x}{2N_e}$. The conditioned drift is therefore $x(1 - x)\,s\coth(2N_esx)$ for $s \ne 0$, and since $s \mapsto s\coth(2N_esx)$ is even and tends to $1/(2N_ex)$ as $s \to 0$, matching the neutral drift, the conditioned diffusion has the same generator for $s$ and $-s$. Its law up to the fixation time is determined by this generator, so the laws of the fixation-conditioned paths coincide for $s$ and $-s$; in particular so do the conditional sojourn densities and the conditional fixation times. The mean age of an allele observed at a given frequency is built from paths from a new mutant to the current frequency, not from the fixation-conditioned law; its symmetry in the sign of $s$ is a separate result. Zhao et al. relate this to the known fact that all statistics of the fixation time under additive selection are, to high accuracy, the same for $s$ and $-s$ (Nei and Roychoudhury 1973; Maruyama 1974, 1977; Taylor et al. 2006), which follows from time-reversal properties (Ewens 2004). The statement uses constant genic selection and constant size. The remark that with dominance the conditioned drift $b + a\,h'/h$ is in general not even in the selection coefficient is this page's own, with no cited source or worked example; it is not part of the statement, and Expansion item 5 asks for an explicit example.

## Depends on

- [Sojourn density conditioned on fixation](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/conditional-green.md)
- [Symmetry of the sojourn density below the current frequency](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/maruyama-below-neg.md)
- [Symmetry of the mean age in the selection coefficient](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-neg.md)
- [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md)
- [Doob h-transform: the Wright–Fisher diffusion conditioned on fixation](../fixation-and-absorption-in-the-wright-fisher-dif/doob-h-transform-process-conditioned-on-fixation.md)

## Expansion

1. The conditioned drift from the Doob transform with $h = P_{fix}$, and its form $x(1 - x)s\coth(2N_esx)$.
2. Evenness of $s\coth(2N_esx)$ in $s$, with the neutral value $1/(2N_ex)$.
3. Uniqueness of the law of the conditioned process given its generator, and equality of the conditioned laws.
4. Consequences for conditional sojourn densities and fixation times; the separate sign symmetry of the mean age.
5. A dominance example in which the conditioned drift differs for $s$ and $-s$.

## Sources

- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, equations (2)–(8), the discussion of large $N_e$, and Appendix A. <https://doi.org/10.1534/genetics.113.156059>
- Original result: T. Maruyama, The age of an allele in a finite population, Genet. Res. 23 (1974), 137–143. <https://doi.org/10.1017/S0016672300014750> The equality of fixation-time statistics for $s$ and $-s$ follows Zhao, Lascoux, Overall and Waxman (2013), who cite it.
