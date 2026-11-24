# Bounds on the generalisation gap

Let $D$ be a probability measure on a measurable space $\mathcal Z$, $\Theta$ a measurable space,
and $\ell : \Theta \times \mathcal Z \to [0, C]$ a jointly measurable loss. Then for every
$n \ge 1$, every $\theta \in \Theta$ and every sample $S = (S_1, \dots, S_n) \in \mathcal Z^n$,
the risk and the empirical risk differ by at most $C$:
$\bigl\lvert \int \ell(\theta, z) \, dD(z) - \frac1n \sum_i \ell(\theta, S_i) \bigr\rvert \le C$.
