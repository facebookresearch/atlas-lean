# Infection–onset–death convolution and the symptomatic case fatality risk

Let $A_{\mathrm{inf}}(t) \ge 0$ be the incidence of infection, $P_{\mathrm{sym}} \in (0, 1]$ the probability that an infection becomes symptomatic, $f_{\mathrm{inc}}$ the probability density of the incubation period, and $f_{\mathrm{od}}$ the probability density of the time from symptom onset to death, both supported on $[0, \infty)$. The symptomatic case fatality risk $\mathrm{sCFR} \in [0, 1]$ is the probability of dying given symptomatic infection. Onset and death incidences are

$$A_{\mathrm{on}}(t) = P_{\mathrm{sym}} \int_{0}^{\infty} A_{\mathrm{inf}}(t - u)\, f_{\mathrm{inc}}(u)\, du, \qquad A_{\mathrm{d}}(t) = \mathrm{sCFR} \int_{0}^{\infty} A_{\mathrm{on}}(t - u)\, f_{\mathrm{od}}(u)\, du,$$

with cumulative cases $\Omega(t) = \int_{-\infty}^{t} A_{\mathrm{on}}$ and deaths $D(t) = \int_{-\infty}^{t} A_{\mathrm{d}}$.

1. **Completed epidemic.** If $\Omega(\infty) < \infty$, then $D(\infty) = \mathrm{sCFR}\cdot \Omega(\infty)$: the final ratio of deaths to symptomatic cases is the sCFR.
2. **Exponential growth.** If $A_{\mathrm{on}}(t) = c\, e^{rt}$ for all $t$ with $c > 0$ and $\int_0^\infty e^{-ru} f_{\mathrm{od}}(u)\, du < \infty$, then

$$\frac{A_{\mathrm{d}}(t)}{A_{\mathrm{on}}(t)} = \frac{D(t)}{\Omega(t)} = \mathrm{sCFR}\cdot M_{\mathrm{od}}(-r), \qquad M_{\mathrm{od}}(-r) = \int_0^\infty e^{-ru} f_{\mathrm{od}}(u)\, du,$$

(for $r > 0$ in the cumulative form). For $r > 0$, $M_{\mathrm{od}}(-r) < 1$, so the crude ratio underestimates the sCFR; for a gamma onset-to-death delay with shape $k$ and rate $b$, $M_{\mathrm{od}}(-r) = (1 + r/b)^{-k}$.
3. **Ascertainment.** If only a fraction $\varepsilon \in (0, 1]$ of symptomatic cases is confirmed while all deaths are counted, confirmed-case ratios are inflated by $1/\varepsilon$; under exponential growth the crude ratio of deaths to confirmed cases is $\mathrm{sCFR}\cdot M_{\mathrm{od}}(-r)/\varepsilon$, so delay and under-ascertainment bias it in opposite directions.

## Proof depends on

- [Moment generating function of the gamma distribution](../../../../Probability/distributions/continuous/gamma-distribution/gamma-mgf/mgf-gamma-measure-of-lt.md)

## Proof sketch

Item 1 is Fubini's theorem: $\int_{\mathbb{R}} A_{\mathrm{d}} = \mathrm{sCFR} \int_0^\infty f_{\mathrm{od}}(u) \int_{\mathbb{R}} A_{\mathrm{on}}(t - u)\, dt\, du = \mathrm{sCFR}\, \Omega(\infty)$. Item 2 follows by substituting $A_{\mathrm{on}}(t - u) = c\, e^{rt} e^{-ru}$, which factors the convolution, and integrating $e^{rs}$ over $(-\infty, t]$ for the cumulative form; $M_{\mathrm{od}}(-r) < 1$ for $r > 0$ because $e^{-ru} < 1$ on $u > 0$ and $f_{\mathrm{od}}$ is a density. The gamma case is the gamma moment-generating function. In the Wuhan analysis these convolutions sit on top of an age-structured, age-of-infection SIR model with relative susceptibilities, and the sCFR is fitted jointly with the ascertainment rate (confirmed cases modelled as Poisson with mean $\varepsilon$ times true onsets), exported traveller cases and charter-flight prevalence, yielding an overall sCFR of about $1.4\%$ under $P_{\mathrm{sym}} = 0.5$.

## Sources

- J. T. Wu, K. Leung, M. Bushman, et al., "Estimating clinical severity of COVID-19 from the transmission dynamics in Wuhan, China", Nature Medicine 26 (2020) 506–510, Methods, transmission model (incidence of infection, onset and death) and likelihood components, <https://doi.org/10.1038/s41591-020-0822-7> (PMC7094929).
- A. C. Ghani, C. A. Donnelly, D. R. Cox, et al., "Methods for estimating the case fatality ratio for a novel, emerging infectious disease", American Journal of Epidemiology 162 (2005) 479–486, <https://doi.org/10.1093/aje/kwi230>.
