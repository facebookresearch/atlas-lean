# Converse of Poisson's law of large numbers for urns (Scottish Book Problem 17)

Let $(\Omega, \mu)$ be a probability space, let $(p_n)_{n \ge 0}$ be real numbers in $[0, 1]$, and let
$(X_n)_{n \ge 0}$ be pairwise independent measurable real random variables on $\Omega$ such that each
$X_n$ almost surely takes only the values $0$ and $1$, and $\mu(X_n = 1) = p_n$. Then for every real
number $L$ and almost every $\omega \in \Omega$: if $\frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega) \to L$ as
$n \to \infty$, then $\frac{1}{n} \sum_{i=0}^{n-1} p_i \to L$.

## Idea

Think of $X_n$ as one draw from the $n$-th of a sequence of urns of unknown composition, a white ball
counting as $1$, and of $p_n$ as the probability of drawing white from the $n$-th urn. Poisson's law of
large numbers says that the observed frequency of white balls is close to the average of the $p_n$.
Ulam's question reverses the inference: if the observed frequency converges, does the average
composition converge to the same limit? Almost surely it does. The centred variables $X_i - p_i$ are
pairwise uncorrelated with variances $p_i(1 - p_i) \le 1/4$, so the strong law of large numbers for
uncorrelated variables with bounded variances (Rajchman's theorem, proved by Chebyshev's inequality
along the squares $n = m^2$, the Borel–Cantelli lemma, and control of the gaps between squares) gives $\frac{1}{n}\sum_{i=0}^{n-1} (X_i - p_i) \to 0$ almost
surely; on that event the two averages have the same limit whenever one of them converges.

## Statements

- [Converse of Poisson's theorem for urns](urn-converse-poisson.md)

## Background

- [Strong law for pairwise independent events](../../laws-of-large-numbers/strong-law-of-large-numbers/pairwise-independent-events/README.md):
  a strong law under pairwise independence only.
