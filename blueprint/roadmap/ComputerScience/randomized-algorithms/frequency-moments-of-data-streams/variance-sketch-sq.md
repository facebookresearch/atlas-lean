# Variance of the AMS sketch

Let $\mu$ be a probability measure on $\Omega$, $\iota$ a finite set, and $(\varepsilon_i)_{i \in \iota}$ measurable random variables with values in $\{-1, 1\}$, mean $0$, and [four-wise independent](four-wise-independent.md): any family of at most four of them is mutually independent. For every stream $l$ of elements of $\iota$, with $m_i$ the number of occurrences of $i$ in $l$ and $Z = \sum_t \varepsilon_{a_t} = \sum_i m_i \varepsilon_i$ its one-pass sketch, the estimator $X = Z^2$ of $F_2(l)$ satisfies

$$\operatorname{Var}(X) = 2 \sum_{i \ne j} m_i^2 m_j^2 = 4 \sum_{i < j} m_i^2 m_j^2,$$

the first sum running over ordered pairs of distinct indices, which needs no order on $\iota$.

Four-wise independence is what makes $\mathbb{E}[\varepsilon_i \varepsilon_j \varepsilon_k \varepsilon_l]$ vanish unless the indices pair up; the source computes $\mathbb{E}[X^2] = \sum_i m_i^4 + 6 \sum_{i<j} m_i^2 m_j^2$.

## Informally uses

- [The one-pass sketch is linear in the frequencies](sketch-eq-sum-count-mul.md): rewrites $Z$ as $\sum_i m_i \varepsilon_i$.
- [Variance of the AMS estimator](variance-sq-weighted-sum.md): the same identity for arbitrary real weights.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, proof of Theorem 2.2.
