# Concentration of the product estimator

Let $n \ge 1$ and $q \ge 1$ be integers, $0 < \varepsilon \le 1$ and $\eta > 0$, and let $a = \lceil 27qn/(\eta\varepsilon^2) \rceil$. For each stage $k = 1, \dots, n$ let $r_k \ge 1/(eq)$, and let $W_k$ be the fraction of successes in $a$ independent Bernoulli trials with a common success probability $p_k$ satisfying $|p_k - r_k| \le \varepsilon/(6eqn)$, all trials of all stages independent. Then the *product estimator* $W = \prod_k W_k$ satisfies

$$
\Pr\Big[(1-\varepsilon)\prod_k r_k \le W \le (1+\varepsilon)\prod_k r_k\Big] \ge 1 - \eta.
$$

## Proof sketch

Each $W_k$ has $\operatorname{Var}(W_k) \le \mathbb{E}(W_k)/a$, and $r_k \ge 1/(eq)$ makes the relative bias of $\mathbb{E}(W_k)$ at most $\varepsilon/(6n)$. Independence across stages makes the mean and second moment of $W$ the products of the stage means and second moments, so $\operatorname{Var}(W)/\mathbb{E}(W)^2 = \prod_k (1 + \operatorname{Var}(W_k)/\mathbb{E}(W_k)^2) - 1$, which is small by the choice of $a$. Chebyshev's inequality bounds the relative deviation of $W$ from its mean, and the per-stage bias moves the mean by at most a small multiple of $\varepsilon$.

The following general form is derived here and is not stated in the cited source. Let each stage have a distribution $\mu_k$ on a finite set $S$, an event $A_k \subseteq S$ and a number $r_k \ge b > 0$; draw $a$ independent samples from each $\mu_k$, all independent, and let $\hat r_k$ be the fraction of the stage-$k$ samples in $A_k$ and $\hat R = \prod_k \hat r_k$. Then $\mathbb{E}[\hat R] = \prod_k \mu_k(A_k)$ and $\mathbb{E}[\hat r_k^2] = \mu_k(A_k)^2 + \mu_k(A_k)(1 - \mu_k(A_k))/a$, and if $0 < \varepsilon \le 1$, $\eta > 0$, $|\mu_k(A_k) - r_k| \le \frac{\varepsilon}{6n} r_k$ for every $k$ and $48 n \le 5\eta\varepsilon^2 a b$, the same two-sided bound holds for $\hat R$ with probability at least $1 - \eta$. The relative variance is then $\prod_k (1 + \frac{1 - \mu_k(A_k)}{a\,\mu_k(A_k)}) - 1 \le e^{6n/(5ab)} - 1$, since $\mu_k(A_k) \ge \frac56 b$. The statement above is the case $b = 1/(eq)$, where $5\eta\varepsilon^2 ab \ge 135n/e \ge 48n$; any larger number of samples per stage also works.

## Proof depends on

- [Chebyshev's inequality](../../moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017, proof of Theorem 14.14, (14.24)-(14.27).
