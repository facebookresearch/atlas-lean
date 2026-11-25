# James–Stein dominance

For $p \ge 3$ the [James–Stein estimator](james-stein.md) has strictly smaller quadratic risk than $X$ at every mean: $\mathbb E \|\delta(X) - \theta\|^2 < p$ for all $\theta \in \mathbb R^p$, so $X$ is inadmissible under squared error loss. Johnstone's draft derives this from equation (2.64). Efron (2021), Theorem 1, which Efron credits to James and Stein (1961), states the same conclusion for the variant that shrinks towards the grand mean, with $N \ge 4$; this page is the shrink-towards-zero version with $p \ge 3$, and [grand-mean dominance](integral-james-stein-grand-mean-risk-lt.md) is the grand-mean version.

## Informally uses

- [Risk of the James–Stein estimator](integrable-and-integral-james-stein-risk.md): the risk is $p$ minus the positive quantity $(p - 2)^2\, \mathbb E\|X\|^{-2}$.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
- B. Efron, "Empirical Bayes: Concepts and Methods", author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
- W. James and C. Stein, "Estimation with quadratic loss", *Proc. Fourth Berkeley Symp. Math. Statist. Probab.*, Vol. 1 (1961) 361–379 (cited for attribution; not consulted for numbering).
