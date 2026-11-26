# Optimal copy number under an epistatic diversity benefit and copy cost

**Fitness model.** An individual with $y \ge 2$ gene copies carrying $x \le y$ distinct alleles has fitness

$$\omega(x, y) = (1 + s_x)^{\sum_{k=0}^{x-1}\beta_x^k}\,(1 - s_y)^{\sum_{k=0}^{y-3}\beta_y^k},$$

with selection coefficients $0 < s_x, s_y \ll 1$ and epistasis parameters $0 < \beta_x \le 1 \le \beta_y$: each additional distinct allele helps less (diminishing returns), each additional copy beyond the two single-copy baseline costs more (synergistic epistasis). For fixed $y$ fitness is maximal at $x = y$; without epistasis it is monotone in $y$.

**Optimal copy number.** In the all-distinct ($x = y$) model with $\beta_x = 1 - \varepsilon$, $\beta_y = 1 + \varepsilon$, fitness is approximately $\omega(y) = e^{f(y)}$ with

$$f(y) = \frac{s_x + s_y}{\varepsilon} - \frac{s_x}{\varepsilon}e^{-\varepsilon y} - \frac{s_y}{\varepsilon}e^{\varepsilon(y-2)},$$

maximized at

$$y^* \approx 1 + \frac{\ln(s_x/s_y)}{2\varepsilon},$$

so an interior optimum $y^* > 2$ requires $s_x > s_y$ (benefit of diversity exceeding the copy cost). A second-order expansion about $y^*$ gives the quadratic (Krüger–Vogel) fitness

$$\tilde\omega(y) = 1 - \tilde s\,(y - y^*)^2, \qquad \tilde s = \varepsilon\,e^{-\varepsilon}\sqrt{s_x s_y},$$

which is negative beyond $y_o = y^* + 1/\sqrt{\tilde s}$, making the copy-number recursion with selection and unequal recombination a finite system.

**Example.** For $s_x = 0.02$, $s_y = 0.005$, $\varepsilon = 0.05$: $y^* = 1 + \ln 4/0.1 \approx 14.86$ and $\tilde s \approx 4.7 \times 10^{-4}$.

## Depends on

- [Neutral copy-number distribution under unequal recombination](neutral-gamma-copy-number-distribution-under-unequal-recombination.md)

## Expansion

Using $\ln(1 \pm s) \approx \pm s$ and the geometric sums $\sum_{k<y}(1 - \varepsilon)^k \approx (1 - e^{-\varepsilon y})/\varepsilon$, $\sum_{k \le y-3}(1+\varepsilon)^k \approx (e^{\varepsilon(y-2)} - 1)/\varepsilon$ gives $f$. Setting $f'(y) = s_x e^{-\varepsilon y} - s_y e^{\varepsilon(y-2)} = 0$ yields $e^{2\varepsilon y^*} = (s_x/s_y)e^{2\varepsilon}$; at that point $s_x e^{-\varepsilon y^*} = s_y e^{\varepsilon(y^*-2)} = e^{-\varepsilon}\sqrt{s_xs_y}$, so $f''(y^*) = -2\varepsilon e^{-\varepsilon}\sqrt{s_xs_y}$, which is $-2\tilde s$. Selection then trades the diffusive spreading of copy number by unequal recombination against stabilizing selection around $y^*$, and lower recombination rates reduce copy-number variance.

## Sources

- M. Otto, Y. Zheng, T. Wiehe, "Recombination, selection, and the evolution of tandem gene arrays", Genetics 221(3) (2022) iyac052, Model, equations (1)–(3), and Results, equations (6)–(7) with Fig. 1, <https://doi.org/10.1093/genetics/iyac052>, PMCID: PMC9252282.
