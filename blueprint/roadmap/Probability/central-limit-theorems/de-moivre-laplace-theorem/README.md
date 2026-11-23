# De Moivre–Laplace theorem

Let $X_0, X_1, \dots$ be independent, identically distributed real random variables on a probability
space $(\Omega, P)$, each almost surely equal to $0$ or $1$, with mean $p$ for some $0 < p < 1$. Write
$S_n = X_0 + \dots + X_{n-1}$, a binomial count with parameters $n$ and $p$. Then the standardized sums
$(S_n - np)/\sqrt{np(1-p)}$ converge in distribution to the standard normal distribution
$\mathcal{N}(0, 1)$ as $n \to \infty$.

## Idea

This is the first central limit theorem, found by de Moivre for $p = 1/2$ and extended by Laplace: the
number of successes in $n$ independent trials, centred by its mean $np$ and divided by its standard
deviation $\sqrt{np(1-p)}$, is approximately standard normal. In the interval form,
$P(a \le (S_n - np)/\sqrt{np(1-p)} \le b)$ tends to the mass of $[a, b]$ under $\mathcal{N}(0, 1)$,
which justifies the normal approximation to binomial probabilities. One proof uses characteristic
functions: the characteristic function of the standardized binomial law is an explicit $n$-th power,
a second-order Taylor bound for the exponential shows that it tends to $e^{-t^2/2}$, and Lévy's
continuity theorem turns this into convergence in distribution.

## Statements

- [De Moivre–Laplace limit theorem, convergence in distribution](de-moivre-laplace-tendsto-in-distributio.md)
- [De Moivre–Laplace limit theorem, interval form](de-moivre-laplace-interval-probability.md): interval-probability form
- [Standardized partial sums](de-moivre-laplace-standardized.md): definition used in the main statement
- [Bernoulli standardization map](standardized-bernoulli.md): definition used in the proof of the main statement
- [Standardized binomial distribution](standardized-binomial.md): definition used in the characteristic-function proof
- [Characteristic function of the real-valued binomial distribution](char-fun-binomial-real.md): lemma used in the characteristic-function proof
- [Affine transformation of a characteristic function](char-fun-map-affine.md): lemma used in the characteristic-function proof
- [Characteristic function of the standardized binomial](char-fun-standardized-binomial.md): lemma used in the characteristic-function proof
- [Convergence of characteristic functions in De Moivre–Laplace](tendsto-char-fun-standardized-binomial.md): the characteristic-function form of the theorem
- [Second-order Taylor remainder bound for the exponential](exp-taylor2-err.md): lemma used in the characteristic-function proof
- [Almost surely $\{0, 1\}$-valued random variables are integrable](integrable-of-ae-eq-zero-or-one.md): lemma used in the proof of the main statement
- [Second moment of a $\{0, 1\}$-valued random variable](integral-sq-eq-integral-of-ae-eq-zero-or.md): lemma used in the proof of the main statement

## Background

- [Lévy's continuity theorem](../../characteristic-functions/levy-continuity-theorem/README.md):
  converts convergence of characteristic functions into convergence in distribution.
- [Variance of the binomial distribution](../../distributions/discrete/binomial-distribution/README.md):
  the scale $\sqrt{np(1-p)}$.
