# Critical population size and error threshold of the Moran quasispecies

Use the sharp-peak Moran model and the notation $\mathrm{Master}(\sigma,\ell,m,q)$ of the [critical curve](critical-curve-of-the-sharp-peak-moran-model.md): alphabet size $\kappa \ge 2$, master fitness $\sigma > 1$, chromosome length $\ell$, population size $m$, per-locus mutation probability $q$. Take $m = \alpha\ell$ and $q = a/\ell$ with $\alpha, a > 0$ and let $\ell \to \infty$.

**Corollary (critical population size; Cerf, Corollary 3.2).**

- If $\alpha < \ln\kappa / \ln\sigma$, then for every $a > 0$, $\lim_{\ell\to\infty} \mathrm{Master}(\sigma,\ell,\alpha\ell,a/\ell) = 0$.
- If $\alpha > \ln\kappa / \ln\sigma$, then there is $a > 0$ with $\lim_{\ell\to\infty} \mathrm{Master}(\sigma,\ell,\alpha\ell,a/\ell) > 0$.

**Corollary (error threshold; Cerf, Corollary 3.3).**

- If $a > \ln\sigma$, then for every $\alpha > 0$, $\lim_{\ell\to\infty} \mathrm{Master}(\sigma,\ell,\alpha\ell,a/\ell) = 0$.
- If $a < \ln\sigma$, then there is $\alpha > 0$ with $\lim_{\ell\to\infty} \mathrm{Master}(\sigma,\ell,\alpha\ell,a/\ell) > 0$.

Consequently, on the sharp peak landscape a quasispecies can emerge only if

$$m > \frac{\ln\kappa}{\ln\sigma}\,\ell \qquad \text{and} \qquad q < \frac{\ln\sigma}{\ell}.$$

The second condition is the finite-population analogue of Eigen's error catastrophe; the first is a minimal population size, proportional to the genome length, that has no counterpart in the infinite-population model.

## Depends on

- [Critical curve of the sharp-peak Moran model](critical-curve-of-the-sharp-peak-moran-model.md)

## Expansion

Both corollaries read off the shape of the function $\phi$ in the critical-curve theorem. The function $\phi$ vanishes for $a \ge \ln\sigma$, so no population size can satisfy $\alpha\,\phi(a) > \ln\kappa$ there: this gives the error threshold. On $(0,\ln\sigma)$ one has $\sup_a \phi(a) = \ln\sigma$, approached as $a \to 0$; the condition $\alpha\,\phi(a) > \ln\kappa$ is achievable for some $a$ exactly when $\alpha\ln\sigma > \ln\kappa$, giving the critical population size. Intuitively, even without mutation pressure a master sequence of selective advantage $\sigma$ persists for a time of order $\sigma^m$ in a population of size $m$, while finding it takes a time of order $\kappa^\ell$.

## Sources

- R. Cerf, *Critical population and error threshold on the sharp peak landscape for a Moran model*, arXiv:1205.3435 (2012). <https://doi.org/10.48550/arXiv.1205.3435>. Published version: Memoirs of the American Mathematical Society 233(1096) (2014), <https://doi.org/10.1090/memo/1096>; locators above refer to the arXiv version.
