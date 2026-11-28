# Size-biased negative-binomial identity and the 80% transmission share

**Notation.** For $R_0 > 0$ and $k > 0$ put $q = k/(k + R_0)$ and let

$$\mathrm{NB}(x; k, q) = \frac{\Gamma(x + k)}{\Gamma(k)\, x!}\, q^{k} (1 - q)^{x}, \qquad x \in \mathbb{N},$$

be the negative-binomial offspring law with mean $R_0$ and dispersion $k$.

**Lemma (size biasing).** For every integer $x \ge 1$,

$$\frac{x}{R_0}\, \mathrm{NB}(x; k, q) = \mathrm{NB}(x - 1; k + 1, q).$$

Equivalently, the offspring count of the infector of a randomly chosen secondary case is distributed as $1 + Y'$ with $Y' \sim \mathrm{NB}(\cdot\,; k + 1, q)$.

**Proportion responsible for 80% of transmission.** Rank infected individuals by their number of secondary cases and interpolate the discrete law piecewise constantly. Let $X > 1$ solve

$$1 - 0.8 = \frac{1}{R_0}\int_0^X \lfloor x \rfloor\, \mathrm{NB}(\lfloor x \rfloor; k, q)\, dx = \int_0^{X - 1} \mathrm{NB}(\lfloor x \rfloor; k + 1, q)\, dx .$$

Then the proportion $p_{80\%}$ of infected individuals who generate 80% of all secondary cases is

$$1 - p_{80\%} = \int_0^X \mathrm{NB}(\lfloor x \rfloor; k, q)\, dx .$$

The left integrals are the share of transmission due to, and the fraction of, individuals with fewer than $X$ offspring; the lemma turns the first into a cumulative distribution function of a negative binomial with dispersion $k + 1$.

## Depends on

- [Negative-binomial offspring probabilities](../../superspreading-and-negative-binomial-offspring/nb-pmf.md)

## Expansion

Since $R_0 = k(1 - q)/q$,

$$\frac{x}{R_0}\mathrm{NB}(x; k, q) = \frac{\Gamma(x + k)}{\Gamma(k)\,(x-1)!}\, q^{k}(1-q)^{x}\cdot \frac{q}{k(1-q)} = \frac{\Gamma\big((x - 1) + (k + 1)\big)}{\Gamma(k + 1)\,(x - 1)!}\, q^{k + 1}(1 - q)^{x - 1},$$

which is $\mathrm{NB}(x - 1; k + 1, q)$. On $[j, j+1)$ the integrand $\lfloor x \rfloor \mathrm{NB}(\lfloor x \rfloor; k, q)/R_0$ equals $\mathrm{NB}(j - 1; k + 1, q)$ for $j \ge 1$ and $0$ for $j = 0$, and the substitution $u = x - 1$ gives the second form of the defining equation. Small $k$ concentrates transmission: the source reports that with $R_0$ between 2 and 3 and $k \approx 0.1$, about 10% of cases account for 80% of secondary transmissions.

## Sources

- A. Endo, Centre for the Mathematical Modelling of Infectious Diseases COVID-19 Working Group, S. Abbott, A. J. Kucharski and S. Funk, *Estimating the overdispersion in COVID-19 transmission using outbreak sizes outside China*, Wellcome Open Research (2020). <https://doi.org/10.12688/wellcomeopenres.15842.3> (PMCID: PMC7338915). Methods: "Model", "Proportion responsible for 80% of secondary transmissions".
- J. O. Lloyd-Smith, S. J. Schreiber, P. E. Kopp and W. M. Getz, *Superspreading and the effect of individual variation on disease emergence*, Nature (2005). <https://doi.org/10.1038/nature04153>
