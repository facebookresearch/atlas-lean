# Conditional moments of a first passage time under fast gamma inactivation

Let $\tau$ be a random variable (a first passage time) whose distribution satisfies the short-time large deviation condition

$$ \lim_{t\to 0^+} t \ln \mathbb{P}(\tau \le t) = -C < 0 $$

for some constant $C > 0$, and let $\sigma$ be an independent gamma random variable (the inactivation time) with rate $\lambda > 0$ and shape $\beta > 0$; $\beta = 1$ is the exponential case. Then for every $m \ge 1$

$$ \mathbb{E}\big[\tau^m \,\big|\, \tau < \sigma\big] \sim \Big(\frac{C}{\lambda}\Big)^{m/2} \quad \text{as } \lambda \to \infty . $$

Consequently

$$ \lambda\, \mathrm{Var}\big[\tau \,\big|\, \tau < \sigma\big] \to 0 \quad \text{and} \quad \frac{\sqrt{\mathrm{Var}[\tau \mid \tau < \sigma]}}{\mathbb{E}[\tau \mid \tau < \sigma]} \to 0 \quad \text{as } \lambda \to \infty , $$

so the successful searchers become deterministic: the conditional first passage time concentrates at $\sqrt{C/\lambda}$. The limit does not depend on the shape $\beta$, so conditioning on beating one exponential clock or a sum of $\beta$ independent exponential clocks with the same rate gives the same fast-inactivation moments.

## Expansion

Write $\mathbb{E}[\tau^m \mid \tau<\sigma] = \mathbb{E}[\tau^m S_\sigma(\tau)]/\mathbb{E}[S_\sigma(\tau)]$ with $S_\sigma$ the gamma survival function, and integrate by parts against $F(t) = \mathbb{P}(\tau\le t)$. As $\lambda \to \infty$ only short times matter; heuristically, where $F(t) \approx e^{-C/t}$ on a logarithmic scale; Laplace's method for integrals of the form $\int e^{-C/t - \lambda t}\,\cdots\,dt$ locates the saddle at $t = \sqrt{C/\lambda}$, and the polynomial prefactors from the gamma density cancel between numerator and denominator. The variance statement follows by applying the theorem with $m = 1$ and $m = 2$ and refining the leading-order cancellation. The result is purely probabilistic and needs no diffusion structure.

## Sources

- Sean D. Lawley, "The Effects of Fast Inactivation on Conditional First Passage Times of Mortal Diffusive Searchers", SIAM Journal on Applied Mathematics 81 (2021), 1–24, <https://doi.org/10.1137/20m1324818>. Published version of arXiv:2003.05515, cited next; locators there refer to the arXiv version.
- S. D. Lawley, "The effects of fast inactivation on conditional first passage times of mortal diffusive searchers", arXiv:2003.05515 (2020), Section 2 (summary) and Section 3 (main theorem, Remark 1 on shape independence, and its corollary on the conditional variance and coefficient of variation). <https://doi.org/10.48550/arXiv.2003.05515>
