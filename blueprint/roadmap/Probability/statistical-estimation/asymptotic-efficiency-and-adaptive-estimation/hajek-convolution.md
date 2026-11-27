# Hájek's convolution theorem

For each $n$ let $(P_{n,h})_{h \in \mathbb R}$ be probability measures on a space $\Omega_n$ (typically $P_{n,h} = P_{\theta + h/\sqrt n}^{\otimes n}$, the local experiments at $\theta$). Assume local asymptotic normality at $0$ with central sequence $\Delta_n$ and information $I > 0$:

- under $P_{n,0}$, $\Delta_n$ converges in law to $N(0, I)$;
- for every $h$, $\log \dfrac{dP_{n,h}}{dP_{n,0}} - \Bigl(h \Delta_n - \dfrac{h^2 I}{2}\Bigr) \to 0$ in $P_{n,0}$-probability.

Let $T_n : \Omega_n \to \mathbb R$ be measurable estimators of the local parameter that are *regular*: for every $h$, the law of $T_n - h$ under $P_{n,h}$ converges weakly to one and the same law $L$. Then there is a probability measure $M$ with

$$L = N(0, I^{-1}) * M .$$

So $N(0, I^{-1})$ is the most concentrated possible limit of a regular estimator, and an estimator is efficient when $M$ is a point mass at $0$. In the i.i.d. case, $T_n = \sqrt n(\hat\theta_n - \theta)$ and regularity says that $\sqrt n(\hat\theta_n - \theta - h/\sqrt n)$ has the same limit under every local alternative $\theta + h/\sqrt n$.

The statement above has a one-dimensional local parameter; the theorem is usually stated for parameters in $\mathbb R^k$. The log-likelihood ratio $\log(dP_{n,h}/dP_{n,0})$ is built from the Radon–Nikodym derivative and read as $0$ instead of $-\infty$ where that derivative vanishes, which does not affect the convergence in probability because, under local asymptotic normality, that event has probability tending to $0$.

## Background

- [Local asymptotic normality of the log-likelihood ratio](../../hypothesis-testing/local-power-of-the-likelihood-ratio-test/tendsto-in-measure-log-likelihood-ratio.md): the expansion assumed above, which holds for smooth i.i.d. models.
- [Le Cam's third lemma](../contiguity-and-le-cam-s-lemmas/tendsto-in-distribution-with-density-exp.md): the change of measure from $P_{n,0}$ to $P_{n,h}$ that standard proofs of the convolution theorem use.
- [Asymptotic normality of maximum likelihood](../asymptotic-normality-of-maximum-likelihood/README.md): under regularity conditions the maximum likelihood estimator attains the limit $N(0, I^{-1})$.
- [Cramér–Rao inequality](../fisher-information-and-the-cram-r-rao-bound/cramer-rao.md): the finite-sample counterpart of the bound $I^{-1}$ for unbiased estimators.

## Sources

- J. Hájek, "A characterization of limiting distributions of regular estimates", *Z. Wahrscheinlichkeitstheorie verw. Geb.* 14 (1970) 323–330.
- P. J. Bickel, "On adaptive estimation", *Ann. Statist.* 10 (1982) 647–671, Section 2 (Conditions R, regular points and efficient estimates).
