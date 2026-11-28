# Stationary distribution of the telegraph model of gene expression

In the two-state (telegraph) model a gene switches from off to on at rate $k_0 > 0$ and from on to off at rate $k_1 > 0$, produces mRNA at rate $v_0 \ge 0$ while on, and each mRNA degrades at rate $d_0 > 0$, so that the Beta parameters $k_0/d_0$ and $k_1/d_0$ below are positive. Iyer-Biswas, Hayot and Jayaprakash (2009, Eq. (10)), solving the master equation through the generating function $G(z) = \sum_m z^m P(m)$ with time measured in units of the mRNA lifetime, give the stationary generating function as a Kummer confluent hypergeometric function; in the present notation

$$G(z) = {}_1F_1\Bigl(\frac{k_0}{d_0};\, \frac{k_0 + k_1}{d_0};\, \frac{v_0}{d_0}(z - 1)\Bigr).$$

The same source describes the mRNA count as a Poisson variable whose parameter is itself random (Eq. (4)). Explicitly, the integral representation ${}_1F_1(a; b; y) = E[e^{yB}]$ with $B \sim \mathrm{Beta}(a, b - a)$, for $b > a > 0$, shows that the stationary mRNA count is Poisson with random mean $(v_0/d_0)B$, $B \sim \mathrm{Beta}(k_0/d_0, k_1/d_0)$; hence $E[m] = \frac{v_0}{d_0}\frac{k_0}{k_0 + k_1}$, which is the product of the fraction of time the gene is on and the mean count of an always-on gene, as stated in the source.

## Expansion

1. The model: the continuous-time Markov chain on (gene state, mRNA count) and its master equation.
2. The generating-function equations for the two gene states and their reduction to Kummer's equation, with the solution regular at $z = 1$ and $G(1) = 1$.
3. The Poisson–Beta mixture from the integral representation of ${}_1F_1$.
4. The mean, variance and Fano factor, and the bimodal regime of slow switching discussed in the source, as corollaries.

## Sources

- S. Iyer-Biswas, F. Hayot and C. Jayaprakash, Stochasticity of gene products from transcriptional pulsing, Phys. Rev. E 79 (2009), 031911, Eqs. (4), (9) and (10). <https://arxiv.org/abs/0711.1141>
- Original result: J. Peccoud and B. Ycart, Markovian modeling of gene-product synthesis, Theor. Popul. Biol. 48 (1995), 222–234. <https://doi.org/10.1006/tpbi.1995.1027> The stationary generating function follows Iyer-Biswas, Hayot and Jayaprakash, Eq. (10).
