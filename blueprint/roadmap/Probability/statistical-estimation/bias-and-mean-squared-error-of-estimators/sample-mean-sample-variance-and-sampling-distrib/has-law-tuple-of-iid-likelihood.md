# Joint law of an i.i.d. sample from a density family

Let $\mu$ be a probability measure on $\Omega$, $\mu_0$ a σ-finite measure on $S$, $(f_\theta)$ a [normalized density family](../../likelihood-and-maximum-likelihood-estimators/normalized-density-family.md) on $S$ with respect to $\mu_0$, and $\theta$ a parameter. If $X_1, \dots, X_n : \Omega \to S$ are mutually independent and each has law $f_\theta\, d\mu_0$, then the tuple $(X_1, \dots, X_n)$ has law

$$\prod_{i=1}^n f_\theta(s_i)\ d\mu_0^{\otimes n}(s_1, \dots, s_n),$$

the product base measure with density the i.i.d. likelihood.
