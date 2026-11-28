# Power-function transducers approach the logarithmic transducer

**Setting.** As in [Threshold-normalized psychometric function of a transducer-noise observer](threshold-normalized-psychometric-function-of-a-transducer-noise-observer.md), a 2AFC observer with transducer $f$, even-symmetric internal noise with CDF $G$, pedestal $x > 0$ and threshold $\Delta x_\theta$ at performance level $p_\theta$ has

$$P(\Delta x) = G\!\left(G^{-1}(p_\theta)\,\frac{f(x+\Delta x) - f(x)}{f(x+\Delta x_\theta) - f(x)}\right).$$

Let $P_q$ be this function for the power transducer $f(x) = x^q$, $q > 0$, and $P_{\log}$ the one for $f(x) = \log x$.

**Lemma 1.** For $a > 0$, $\lim_{q \to 0}(a^q - 1)/q = \ln a$.

**Theorem 4.** For a nonzero pedestal $x > 0$ and every $\Delta x \ge 0$,

$$\lim_{q\to 0}P_q(\Delta x) = P_{\log}(\Delta x) = G\!\left(G^{-1}(p_\theta)\,\frac{\ln(1 + \Delta x/x)}{\ln(1 + \Delta x_\theta/x)}\right),$$

and, with the transducer factor $\beta^{\mathrm{Transducer}} = f'(x+\Delta x_\theta)\,\Delta x_\theta/\big(f(x+\Delta x_\theta) - f(x)\big)$ of the best-fitting Weibull slope (the source's Eq. (17)) and the Weber fraction $W = \Delta x_\theta/x$,

$$\beta^{\mathrm{Transducer}}_q = \frac{W(1+W)^{q-1}}{\big((1+W)^q - 1\big)/q} \ \to\ \frac{W}{(1+W)\ln(1+W)} = \beta^{\mathrm{Transducer}}_{\log} \qquad (q \to 0).$$

## Depends on

- [Threshold-normalized psychometric function of a transducer-noise observer](threshold-normalized-psychometric-function-of-a-transducer-noise-observer.md)

## Expansion

Dividing numerator and denominator of the transducer ratio by $q\,x^q$ gives $\big[((1+\Delta x/x)^q - 1)/q\big]\big/\big[((1+\Delta x_\theta/x)^q - 1)/q\big]$, and Lemma 1 applied to both yields the ratio of logarithms; $G$ and $G^{-1}$ are continuous on the relevant range. The approach is fast: power-function exponents of $0.4$–$0.5$, typical of fits of the Legge–Foley transducer to suprathreshold contrast discrimination, already give psychometric functions practically indistinguishable from those of a log transducer, so such data cannot separate the two models. At zero pedestal the limit does not apply, since $\log$ is not defined at $0$.

## Sources

- K. A. May and J. A. Solomon, "Four theorems on the psychometric function", PLoS ONE 8(10) (2013) e74815, Lemma 1, Theorems 4A–4B and Eqs. (69)–(71), (86)–(92), <https://doi.org/10.1371/journal.pone.0074815>, PMCID PMC3790801.
