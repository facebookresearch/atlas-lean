# Consistent roots of the score equations under a profile crossing

Let $\mu$ be a measure on $\Omega$ (in applications a probability measure) and let the counts
$X_0, X_1, \dots : \Omega \to \mathbb{N}$ be pairwise independent and identically distributed under
$\mu$, with $X_0$ measurable and integrable, and let $\int X_0\, d\mu = \sigma a_0 / b_0$ for some
$\sigma, a_0, b_0 > 0$, the marginal mean of the hierarchy at the true hyperparameters $(a_0, b_0)$
and the common size factor $\sigma$. Assume local identifiability of the shape: for all small
$\varepsilon > 0$ the [population profile shape score](pop-profile-shape-score.md) $\Sigma_\mu$ of
$X_0$ satisfies $\Sigma_\mu(a_0 - \varepsilon) > 0 > \Sigma_\mu(a_0 + \varepsilon)$. Then for
$\mu$-almost every $\omega$, for every $\varepsilon > 0$ and all large $n$, the score equations
$S_a = S_b = 0$ of the first $n$ counts, for the [shape](shape-score.md) and [rate](rate-score.md)
scores at the size factor $\sigma$, have a solution $(\hat a, \hat b)$ with $\hat a, \hat b > 0$,
$|\hat a - a_0| < \varepsilon$ and $|\hat b - b_0| < \varepsilon$: there is a strongly consistent
sequence of roots (Cramér 1946).

The crossing is a hypothesis of the result. For negative binomial counts it follows from the
identity $E\bigl[\sum_{j < X_0} 1/(a_0 + j)\bigr] = \log(1 + \sigma / b_0)$, which says that the
expected shape score vanishes at the truth, together with positivity of the profile information at
$a_0$.
