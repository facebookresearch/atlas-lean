# Logarithmic selection threshold for adaptation on additive landscapes

**Model.** A monomorphic population of size $N$ has genotype $x \in \{0,1\}^n$. Each step a uniformly random site is mutated, and the mutant replaces the resident with Kimura's fixation probability

$$p_{\mathrm{fix}}(\Delta f) = \frac{1 - e^{-2\beta\Delta f}}{1 - e^{-2N\beta\Delta f}},$$

where $\Delta f$ is the fitness difference and $\beta > 0$ the selection strength; time is counted in mutation trials. Additive landscapes are $f_{\mathrm{eq}}(x) = \sum_i x_i$ and, more generally, $f_{\mathrm{add}}(x) = \sum_i w_i x_i$ with $w_i > 0$, $\sum_i w_i = W$.

**Drift.** On $f_{\mathrm{eq}}$ with $x$ ones, the expected progress per trial is

$$\Delta(x) = p_{\mathrm{fix}}(1)\Big[\frac{n-x}{n} - \frac{x}{n}\,e^{-2(N-1)\beta}\Big],$$

using $p_{\mathrm{fix}}(-1)/p_{\mathrm{fix}}(1) = e^{-2(N-1)\beta}$.

**Theorem.**
1. (Sufficiency.) If $2(N-1)\beta \ge \ln(cn)$ for a constant $c > 1$, the expected time to reach the peak $1^n$ of $f_{\mathrm{eq}}$ from any start is at most

$$\frac{1}{p_{\mathrm{fix}}(1)}\Big[\frac{cn}{c-1} + n\ln\frac{cn-1}{c-1}\Big] = \frac{n\ln n + O(n)}{p_{\mathrm{fix}}(1)},$$

and a genotype within $a$ mutations of the peak is reached in expected time $\big(n\ln(n/a) + O(n)\big)/p_{\mathrm{fix}}(1)$, which is linear in $n$ for $a = \Theta(n)$.
2. (Necessity.) If $1 \le N\beta \le \frac{1-\epsilon}{2}\ln n$ for a constant $\epsilon > 0$, then near the peak (at $x \ge n - n^{\epsilon/2}$) the drift is negative, $\Delta(x) \le -c'\beta n^{\epsilon-1}$, and the time to reach the peak is exponential in $n^{\epsilon/2}$ with overwhelming probability.
3. (General additive.) With a critical weight $w^* > \ln(cn)/[2(N-1)\beta]$ and $n^*$ the number of sites with $w_i \le w^*$, fitness at least $W - n^*w^*$ is reached in expected time $(n\ln n + O(n))/p_{\mathrm{fix}}(w^*)$.

So a population climbs an additive peak efficiently only if selection strength grows logarithmically with the number of sites under selection; at fixed $N\beta$ there is a maximum number of sites that can be adapted in polynomial time.

## Depends on

- [Closed form of Kimura's fixation probability](../../population-genetics/moran-model/kimura-fixation-half.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

The variable drift theorem bounds the expected time to go from distance $X_0$ to distance below $a$ by $a/h(a) + \int_a^{X_0} dx/h(x)$ whenever the drift toward the target is at least an increasing positive function $h$ of the distance. Under the threshold, with $z = n - x$ remaining zeros, $\Delta \ge p_{\mathrm{fix}}(1)\,(cz - 1)/(cn) = h(z)$, and integrating gives the $n\ln n$ bound, dominated by the last few beneficial mutations, which are rare ($z/n$) and opposed by many deleterious ones ($x/n$). Below the threshold, deleterious mutations fix often enough that the walk is pushed back in an interval of length $n^{\epsilon/2}$, and the negative drift theorem (with exponentially decaying jump probabilities) gives exponential time. For general weights the large-effect sites behave like the equal-effects case.

## Sources

- J. P. Heredia, B. Trubenová, D. Sudholt, T. Paixão, "Selection limits to adaptive walks on correlated landscapes", Genetics 205:803–825 (2017), Eqs (1)–(5), the general additive analysis with Appendix E (Eq E2), and Appendices B–D, <https://doi.org/10.1534/genetics.116.189340>, PMCID PMC5289853.
