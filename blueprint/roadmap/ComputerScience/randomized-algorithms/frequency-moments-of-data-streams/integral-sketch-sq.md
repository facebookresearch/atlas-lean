# The AMS sketch is unbiased for $F_2$

Let $\mu$ be a probability measure on $\Omega$, $\iota$ a finite set, and $(\varepsilon_i)_{i \in \iota}$ measurable random variables with values in $\{-1, 1\}$, mean $0$, and [four-wise independent](four-wise-independent.md): any family of at most four of them is mutually independent. For every stream $l = (a_1, \dots, a_m)$ of elements of $\iota$, the one-pass sketch $Z = \sum_{t=1}^m \varepsilon_{a_t}$ satisfies

$$\mathbb{E}[Z^2] = F_2(l) = \sum_{i \in \iota} m_i^2,$$

where $m_i$ is the number of occurrences of $i$ in $l$. The empty stream is allowed: then $Z = 0$ and $F_2 = 0$.

The source notes that this step needs only pairwise independence; four-wise independence is needed for the variance.

## Informally uses

- [The one-pass sketch is linear in the frequencies](sketch-eq-sum-count-mul.md): rewrites $Z$ as $\sum_i m_i \varepsilon_i$.
- [Unbiasedness of the AMS estimator](integral-sq-weighted-sum.md): the same identity for arbitrary real weights.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, proof of Theorem 2.2.
