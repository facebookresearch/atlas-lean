# Mean of the inverse squared norm of a standard Gaussian vector

For $p \ge 3$ and $X \sim \mathcal N_p(0, I)$,

$$\mathbb E\, \|X\|^{-2} = \frac{1}{p - 2},$$

the mean of the reciprocal of a $\chi^2_p$ variable (Johnstone's draft, equation (2.67)). Efron (2021) uses the same fact with $N - 1$ degrees of freedom, $\mathbb E\{(\chi^2_{N-1})^{-1}\} = (N - 3)^{-1}$, below equation (3.13). The proof reads it off the [risk of the James–Stein estimator](integrable-and-integral-james-stein-risk.md) at $\theta = 0$, where the risk can also be computed directly as $p - 2(p - 2) + (p - 2)^2\, \mathbb E\|X\|^{-2}$.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
- B. Efron, "Empirical Bayes: Concepts and Methods", author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
