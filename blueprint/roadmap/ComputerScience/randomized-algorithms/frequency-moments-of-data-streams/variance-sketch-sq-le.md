# Variance bound for the AMS sketch

Let $\mu$ be a probability measure on $\Omega$, $\iota$ a finite set, and $(\varepsilon_i)_{i \in \iota}$ measurable random variables with values in $\{-1, 1\}$, mean $0$, and [four-wise independent](four-wise-independent.md): any family of at most four of them is mutually independent. For every stream $l$ of elements of $\iota$, its one-pass sketch $Z$ satisfies

$$\operatorname{Var}(Z^2) \le 2\, F_2(l)^2 .$$

For $\lambda > 0$ and an integer $s \ge 16/\lambda^2$ (for instance $s = \lceil 16/\lambda^2 \rceil$), Chebyshev's inequality shows that the mean of $s$ independent copies of $Z^2$ is within $\lambda F_2$ of $F_2$ with probability at least $7/8$.

## Informally uses

- [The one-pass sketch is linear in the frequencies](sketch-eq-sum-count-mul.md): rewrites $Z$ as $\sum_i m_i \varepsilon_i$.
- [Variance bound for the AMS estimator](variance-sq-weighted-sum-le.md): the bound $2 (\sum_i m_i^2)^2$ for arbitrary real weights.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, proof of Theorem 2.2 ("$\operatorname{Var}(X) \le 2F_2^2$").
