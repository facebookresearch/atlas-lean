# James–Stein estimator

The James–Stein estimator of the mean of $\mathcal N_p(\theta, I)$ is

$$\delta(x) = \Bigl(1 - \frac{p - 2}{\|x\|^2}\Bigr) x,$$

Johnstone's draft, equation (2.63). At $x = 0$ the convention $a / 0 = 0$ makes the factor $1$, so $\delta(0) = 0$; for $p \ge 1$ this point has probability zero under $\mathcal N_p(\theta, I)$ (for $p = 0$ it is the only point). Efron (2021), Theorem 1, which Efron credits to James and Stein (1961), states the variant that shrinks towards the grand mean $\bar x$ with factor $1 - (N - 3)\sigma_0^2/S$: see [the grand-mean estimator](james-stein-grand-mean.md).

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
- B. Efron, "Empirical Bayes: Concepts and Methods", author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
- W. James and C. Stein, "Estimation with quadratic loss", *Proc. Fourth Berkeley Symp. Math. Statist. Probab.*, Vol. 1 (1961) 361–379 (cited for attribution; not consulted for numbering).
