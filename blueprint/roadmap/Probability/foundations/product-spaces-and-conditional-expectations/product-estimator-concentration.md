# Concentration of the product estimator

Let $n \ge 1$ stages be given, each with a distribution $\mu_k$ on a finite set $S$, an event $A_k \subseteq S$ and a number $r_k \ge b > 0$. Draw $a$ independent samples from each $\mu_k$, all independent, let $\hat r_k$ be the fraction of the stage-$k$ samples in $A_k$, and let $\hat R = \prod_k \hat r_k$ be the *product estimator*. Then $\mathbb{E}[\hat R] = \prod_k \mu_k(A_k)$ and $\mathbb{E}[\hat r_k^2] = \mu_k(A_k)^2 + \mu_k(A_k)(1 - \mu_k(A_k))/a$. If $0 < \varepsilon \le 1$, $\eta > 0$, $|\mu_k(A_k) - r_k| \le \frac{\varepsilon}{6n} r_k$ for every $k$, and $48 n \le 5\eta\varepsilon^2 a b$, then

$$
\Pr\Big[(1-\varepsilon)\prod_k r_k \le \hat R \le (1+\varepsilon)\prod_k r_k\Big] \ge 1 - \eta.
$$

## Proof sketch

Independence across stages makes the mean and second moment of $\hat R$ the products of the stage means and second moments. The relative variance is then $\prod_k (1 + \frac{1 - \mu_k(A_k)}{a\,\mu_k(A_k)}) - 1 \le e^{n/(ab')} - 1$ for $b'$ close to $b$, which is small under the sample-size condition. Chebyshev's inequality bounds the relative deviation of $\hat R$ from its mean, and the relative error $\varepsilon/(6n)$ per stage moves the mean by at most a small multiple of $\varepsilon$.

## Proof depends on

- [Chebyshev's inequality](../../moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
