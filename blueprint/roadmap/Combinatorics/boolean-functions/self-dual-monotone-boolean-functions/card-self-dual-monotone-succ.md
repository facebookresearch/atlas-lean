# Counting self-dual monotone functions on $n + 1$ variables

For every $n \ge 0$, the
number of self-dual monotone Boolean functions on $n + 1$ variables equals the number of
monotone Boolean functions $b$ on $n$ variables with $b \le b^*$, where $b^*$ is the dual of $b$
and functions are ordered pointwise. Moreover, for a permutation $\pi$ of the $n$ coordinates
write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, and let $R$ be any finite set of
monotone Boolean functions on $n$ variables such that for every monotone $f$ there is exactly
one $b \in R$ with $f = b^\pi$ for some permutation $\pi$. Then the number of self-dual
monotone Boolean functions on $n + 1$ variables equals $\sum_{b \in R,\ b \le b^*} \gamma(b)$,
where $\gamma(b)$ is the number of distinct functions $b^\pi$ as $\pi$ ranges over all
permutations.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 6 (`jis-2025-25.6.5-thm-6`).
