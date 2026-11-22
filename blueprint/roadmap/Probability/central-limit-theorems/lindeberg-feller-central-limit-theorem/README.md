# Lindeberg–Feller central limit theorem

Let $\mu$ be a probability measure on $\Omega$ and let $X_{n,k}$ ($n \in \mathbb{N}$, $0 \le k < n$) be
a triangular array of measurable real random variables on $\Omega$ such that for each $n$ the variables
$X_{n,0}, \dots, X_{n,n-1}$ are independent, each $X_{n,k}$ has mean $0$, and each $X_{n,k}^2$ is
integrable (expectations are taken under $\mu$). Suppose that for some $\sigma > 0$ the row variances
$\sum_{k < n} \mathbb{E}[X_{n,k}^2]$ converge to $\sigma^2$, and that the array satisfies the Lindeberg
condition: for every $\varepsilon > 0$,

$$\sum_{k < n} \mathbb{E}\big[X_{n,k}^2 \, \mathbf{1}\{|X_{n,k}| > \varepsilon\}\big] \to 0 \qquad (n \to \infty).$$

Then the row sums $S_n = \sum_{k < n} X_{n,k}$ converge in distribution to the Gaussian law
$N(0, \sigma^2)$: for every bounded continuous $f : \mathbb{R} \to \mathbb{R}$,
$\mathbb{E}[f(S_n)] \to \int_{\mathbb{R}} f \, dN(0, \sigma^2)$ as $n \to \infty$.

## Idea

The Lindeberg condition says that no single summand carries a non-negligible part of the variance: the
part of the variance coming from values larger than $\varepsilon$ vanishes in the limit. Under this
condition the summands need not be identically distributed, and the sum is still asymptotically
Gaussian. The classical central limit theorem is the special case $X_{n,k} = X_k/\sqrt{n}$ for an
i.i.d. sequence with mean $0$ and variance $\sigma^2$, where the condition follows from dominated
convergence. One proof compares the characteristic function of $S_n$, a product of characteristic
functions of the summands, with $e^{-\sigma^2 t^2/2}$, using a second-order Taylor bound for
$e^{ix}$ and a bound comparing a product $\prod (1 + a_k)$ with $\exp(\sum a_k)$. Feller proved the
converse: if the largest variance in row $n$ tends to $0$ and $S_n$ converges to $N(0, \sigma^2)$, the
Lindeberg condition holds. The statement above is Lindeberg's direction.

## Statements

- [Lindeberg–Feller central limit theorem](lindeberg-feller-clt-triangular.md)
- [Lindeberg condition for a triangular array](lindeberg-condition-triangular.md): definition used in the main statement
- [Analytic core of the Lindeberg–Feller theorem](lindeberg-char-fun-product-tendsto.md): lemma used in the proof of the main statement
- [Comparing a finite product with the exponential of a sum](prod-one-add-sub-exp-sum-le.md): lemma used in the proof of the analytic core
- [Second-order Taylor bound for the imaginary exponential](norm-exp-of-real-mul-i-sub-one-sub-le.md): elementary estimate of the kind used in the characteristic-function proof

## Background

- [Lévy's continuity theorem](../../characteristic-functions/levy-continuity-theorem/README.md):
  converts convergence of characteristic functions into convergence in distribution.

## Sources

- J. W. Lindeberg, "Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung",
  Mathematische Zeitschrift (1922).
- W. Feller, "Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung", Mathematische
  Zeitschrift (1935).
