# Normalized KL test bound

Let $\mu$ and $\nu$ be probability measures on a measurable space and let $f$ be a measurable real function with $f$ integrable for $\mu$, $e^{f}$ integrable for $\nu$, and

$$\int e^{f}\, d\nu = 1.$$

Then

$$\operatorname{ofReal}\!\left(\int f\, d\mu\right) \le \mathrm{KL}(\mu \,\|\, \nu)$$

in $[0, \infty]$, where $\operatorname{ofReal}(r) = \max(r, 0)$ and the divergence is in nats ($+\infty$ unless $\mu \ll \nu$ with integrable log-likelihood ratio).
