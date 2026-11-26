# Characteristic firing-rate mean and variance under dual homeostasis

Let a neuron's firing rate $r(t; a, b)$ depend on two slow homeostatic variables $a, b$ (for example intrinsic excitability and a synaptic scaling factor, the latter on a log scale) that obey

$$\frac{\tau_a}{\epsilon} \dot a = f_a(r_a) - f_a(r), \qquad \frac{\tau_b}{\epsilon} \dot b = f_b(r_b) - f_b(r),$$

with target rates $r_a, r_b$, time constants $\tau_a, \tau_b > 0$, a small time-scale separation $\epsilon > 0$, and smooth increasing bounded control functions $f_a, f_b$ with bounded derivatives. Assume that for fixed $(a, b)$ the rate is ergodic with stationary distribution $P(r; a, b)$ of mean $\mu(a, b)$ and variance $\nu(a, b)$, and consider the **averaged system** $\frac{\tau_a}{\epsilon} \dot a = F_a(a,b) := f_a(r_a) - \langle f_a(r) \rangle_{(a,b)}$, $\frac{\tau_b}{\epsilon} \dot b = F_b(a,b) := f_b(r_b) - \langle f_b(r) \rangle_{(a,b)}$. Put

$$K_a = \frac{f_a''(r_a)}{f_a'(r_a)}, \quad K_b = \frac{f_b''(r_b)}{f_b'(r_b)}, \quad k = \frac{K_a + K_b}{K_a - K_b - K_a K_b (r_b - r_a)},$$

assuming $K_a \ne K_b$ and the denominator of $k$ nonzero.

**Theorem (Theorem 1 of the source).** On a domain of states $(a, b)$ for which $f_a''$ and $f_b''$ are constant on the support of $P(r; a, b)$, the fixed points of the averaged system are exactly the states at which $\mu(a, b) = \mu^*$ and $\nu(a, b) = \nu^*$, where

$$\mu^* = \frac{r_a + r_b}{2} + \frac{r_b - r_a}{2} k, \qquad \nu^* = \frac{r_b - r_a}{K_b - K_a} \left( 2 - \frac{r_b - r_a}{4} \Big( (K_b - K_a)(1 + k^2) - 2 (K_a + K_b) k \Big) \right).$$

**Corollary (Corollary 1 of the source).** With $K = \max(|K_a|, |K_b|)$, as $K |r_b - r_a| \to 0$ and $K^2 |r_b - r_a| / |K_b - K_a| \to 0$,

$$\mu^* \approx \frac{r_a + r_b}{2} - \frac{r_b - r_a}{2} \frac{K_a + K_b}{K_b - K_a}, \qquad \nu^* \approx 2 \frac{r_b - r_a}{K_b - K_a}.$$

So a fixed point with positive variance requires $r_b - r_a$ and $K_b - K_a$ of the same sign, and the characteristic variance grows in proportion to the separation of the targets.

## Expansion

With $f_a$ quadratic on the support, $\langle f_a(r) \rangle = f_a(r_a) + f_a'(r_a)(\mu - r_a) + \tfrac12 f_a''(r_a)\big(\nu + (\mu - r_a)^2\big)$, so $F_a = 0$ reads $K_a \nu + 2(\mu - r_a) + K_a (\mu - r_a)^2 = 0$, and similarly for $b$. Eliminating $\nu$ between the two equations gives $\mu^*$, and their difference then gives $\nu^*$. The fixed-point conditions involve the whole rate distribution only through its first two moments, which is why two feedbacks can pin both the mean and the variance, while a single feedback can only reach a one-parameter family of (mean, variance) pairs.

Example (Sect. 2 of the source): for the rate model $\tau_r \dot r = -r + g\,(\phi + \sigma \xi(t)) + x$ with white noise $\xi$, the rate is an Ornstein-Uhlenbeck process with $\mu = g\phi + x$ and $\nu = g^2 \sigma^2 / (2\tau_r)$. With linear intrinsic control $f_x(r) = r$ and quadratic multiplicative synaptic control $\tau_g \dot g = g (r_g^2 - r^2)$, the averaged system has a fixed point with $g^* > 0$ if and only if $r_g > r_x$; it is asymptotically stable, with $\mu^* = r_x$ and $\nu^* = r_g^2 - r_x^2$ independent of the input statistics $\phi, \sigma$, in agreement with the formulas above ($K_x = 0$, $K_g = 1/r_g$, $k = -1$).

## Sources

- J. Cannon and P. Miller, *Stable control of firing rate mean and variance by dual homeostatic mechanisms*, Journal of Mathematical Neuroscience 7 (2017), 1. DOI: <https://doi.org/10.1186/s13408-017-0043-7>. PMCID: PMC5264207.
