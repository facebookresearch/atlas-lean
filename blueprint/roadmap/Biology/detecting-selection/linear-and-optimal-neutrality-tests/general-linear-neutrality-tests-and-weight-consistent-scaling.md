# General linear neutrality tests and weight-consistent scaling

Let $\xi_i$ ($1 \le i \le n-1$) be the unfolded site frequency spectrum of a sample of $n$ haploid sequences of length $L$, i.e. the number of segregating sites at which the derived allele has count $i$. Under the standard neutral Wright–Fisher model $E(\xi_i) = \theta L / i$, with $\theta$ the scaled mutation rate per base. For real weights $\Omega_1, \dots, \Omega_{n-1}$ with

$$\sum_{i=1}^{n-1} \Omega_i = 0,$$

the statistic

$$T_\Omega = \frac{\sum_{i=1}^{n-1} i\,\Omega_i\,\xi_i}{\sqrt{\operatorname{Var}\!\left(\sum_{j=1}^{n-1} j\,\Omega_j\,\xi_j\right)}}$$

has $E(T_\Omega) = 0$ and $\operatorname{Var}(T_\Omega) = 1$ under neutrality, and every centred, unit-variance linear test in the spectrum has this form. Equivalently, if $\hat\theta_\omega = L^{-1}\sum_i i\,\omega_i\,\xi_i$ and $\hat\theta_{\omega'}$ are two unbiased estimators of $\theta$ (weights with $\sum_i \omega_i = \sum_i \omega'_i = 1$), then $T_\Omega$ with $\Omega_i = \omega_i - \omega'_i$ is the standardized difference $\hat\theta_\omega - \hat\theta_{\omega'}$.

A family of weights indexed by $n$ is weight-consistent if, for a fixed weight function $\Omega(f)$ on $(0,1)$ with $\int_0^1 \Omega(f)\,df = 0$, $\Omega_i^{(n)} \simeq \Omega(i/n)$. Two centred implementations are

$$\Omega_i^{(n)} = \Omega\!\left(\tfrac{i}{n}\right) - \frac{1}{n-1}\sum_{j=1}^{n-1}\Omega\!\left(\tfrac{j}{n}\right)
\quad\text{and}\quad
\Omega_i^{(n)} = \frac{\omega(i/n)}{\sum_{j=1}^{n-1}\omega(j/n)} - \frac{\omega'(i/n)}{\sum_{j=1}^{n-1}\omega'(j/n)},$$

which differ by $O(1/n)$ when $\Omega$ is bounded and piecewise continuous; for weights diverging like $1/f$ or faster (as with Watterson's estimator), only the second, normalized form avoids a dependence on the population-size cutoff. For example, Fay and Wu's $H$ corresponds to $\omega(f) = 1$, $\omega'(f) = 2f$, i.e. $\Omega(f) = 1 - 2f$.

## Depends on

- [Tajima's D](../tajima-s-d/tajima-d.md)
- [Expected site frequency spectrum](../../coalescent-theory/expected-site-frequency-spectrum/integral-sfs.md)

## Expansion

Centredness follows by substituting $E(\xi_i) = \theta L/i$: the numerator has mean $\theta L \sum_i \Omega_i = 0$. Because $i/n$ is an unbiased estimator of the population frequency of a derived allele, weights that depend on $i$ only through $i/n$ give the same relative importance to each frequency class at every sample size, so the sign and interpretation of the test do not drift with $n$. Tests such as Achaz's admixture and bottleneck tests, whose weights are not functions of $i/n$, can change sign as $n$ grows; rescaling their parameters (for instance $e^{-\alpha i}$ replaced by $e^{-\beta i/n}$) restores consistency.

## Sources

- S. E. Ramos-Onsins, G. Marmorini, G. Achaz and L. Ferretti, "A general framework for neutrality tests based on the site frequency spectrum", *Genes* 14 (2023), 1714, Section 1, Eq. (1), and Sections 2.1–2.2, Eqs. (3)–(11). <https://doi.org/10.3390/genes14091714> (PMC10531300)
