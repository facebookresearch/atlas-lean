# Two-class Gaussian discriminant analysis has a logistic posterior

Consider Gaussian discriminant analysis on $\mathbb{R}^\iota$, for a finite index set $\iota$, with the two classes $\{\mathrm{true}, \mathrm{false}\}$, prior weights $\pi_{\mathrm{true}}, \pi_{\mathrm{false}} > 0$, class means $\mu_{\mathrm{true}}, \mu_{\mathrm{false}}$ and a shared precision matrix $S$ that is positive definite. Then for every $x$ the posterior probability of $\mathrm{true}$ is

$$P(\mathrm{true} \mid x) = \sigma\Bigl( \bigl(S(\mu_{\mathrm{true}} - \mu_{\mathrm{false}})\bigr) \cdot x + \log\frac{\pi_{\mathrm{true}}}{\pi_{\mathrm{false}}} - \tfrac12\bigl(\mu_{\mathrm{true}}^\top S \mu_{\mathrm{true}} - \mu_{\mathrm{false}}^\top S \mu_{\mathrm{false}}\bigr) \Bigr),$$

where $\sigma(z) = 1 / (1 + e^{-z})$ is the logistic function.
