# Threshold-normalized psychometric function of a transducer-noise observer

**Model.** In a 2AFC task a pedestal stimulus of value $x$ and a target of value $x + \Delta x$, $\Delta x \ge 0$, are presented; the observer transduces each by a strictly increasing function $f$, adds internal noise and picks the larger internal value. The difference of the two noisy internal values is $f(x + \Delta x) - f(x)$ plus a noise sample with an even-symmetric density, whose CDF is $G$. The probability of a correct response is

$$P(\Delta x) = G\big(f(x+\Delta x) - f(x)\big),$$

which rises from $1/2$ at $\Delta x = 0$. Let the threshold $\Delta x_\theta > 0$ be the stimulus difference at which $P(\Delta x_\theta) = p_\theta$ for a chosen performance level $p_\theta \in (1/2, 1)$.

**Theorem 1.** (1) The psychometric function can be written

$$P(\Delta x) = G\!\left(G^{-1}(p_\theta)\,\frac{f(x+\Delta x) - f(x)}{f(x+\Delta x_\theta) - f(x)}\right).$$

(2) Replacing $f$ by $kf$, $k > 0$ (transducer gain), leaves this expression unchanged. (3) Replacing $G(z)$ by $G(z/k)$ (noise spread) leaves it unchanged. With zero pedestal and $f(0) = 0$ it reduces to $P(\Delta x) = G\big(G^{-1}(p_\theta)\,f(\Delta x)/f(\Delta x_\theta)\big)$.

**Linear limit (fine thresholds).** If $f$ is differentiable at the pedestal with $0 < f'(x) < \infty$, then for each fixed ratio $s = \Delta x/\Delta x_\theta$,

$$\frac{f(x + s\Delta x_\theta) - f(x)}{f(x+\Delta x_\theta) - f(x)} \to s \quad (\Delta x_\theta \to 0),$$

so the threshold-normalized psychometric function tends to $G(G^{-1}(p_\theta)\,s)$, that of a linear transducer. If moreover $f'$ exists near $x$ and is continuous at $x$, the transducer factor of the best-fitting Weibull slope, $\beta^{\mathrm{Transducer}} = f'(x+\Delta x_\theta)\,\Delta x_\theta/\big(f(x+\Delta x_\theta) - f(x)\big)$ (the source's Eq. (17)), tends to its linear-transducer value $1$ (Theorem 3). The conclusion can fail where $f'(x) \in \{0, \infty\}$, as for power-function transducers at zero pedestal (contrast detection).

## Expansion

Evaluating the model at threshold gives $G^{-1}(p_\theta) = f(x + \Delta x_\theta) - f(x)$, so multiplying the argument of $G$ by $G^{-1}(p_\theta)/(f(x+\Delta x_\theta) - f(x)) = 1$ gives part (1). A gain $k$ cancels in the ratio, and rescaling the noise multiplies $G^{-1}$ by $k$ and divides the argument by $k$, which gives (2)–(3); hence any standard form of $f$ and $G$ can be used once the threshold is fixed. For a linear observer the psychometric function on a linear abscissa traces the positive half of the noise CDF. Fitting a Weibull function to the psychometric function, its slope parameter $\beta$ factors approximately into a noise factor and a transducer factor (Theorem 2); for a power transducer $f(x) = x^q$ at zero pedestal the transducer factor is $q$, recovering Pelli's relation $\beta \approx q\,\beta_{\text{noise}}$.

## Sources

- K. A. May and J. A. Solomon, "Four theorems on the psychometric function", PLoS ONE 8(10) (2013) e74815, Eqs. (3)–(6), (11), (14) and Theorems 1–3, <https://doi.org/10.1371/journal.pone.0074815>, PMCID PMC3790801.
