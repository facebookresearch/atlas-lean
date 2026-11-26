# The asymptotic Plotkin bound

Let $C$ be a code of length $n$ over an alphabet of $q \ge 2$ letters with minimum distance at least $d > 0$, where $q d \le (q - 1) n$. Then

$$\log_q |C| \le n - \frac{q d}{q - 1} + 2 + \log_q d.$$

Consequently, for a family of codes with lengths $n_s \to \infty$ and relative distance at least $\delta$, $0 \le \delta \le 1 - 1/q$, for every $\varepsilon > 0$ eventually $\log_q |C_s| \le (1 - \frac{q}{q-1}\delta + \varepsilon)\, n_s$: the rate is at most $1 - \frac{q}{q-1}\delta + o(1)$.

## Proof sketch

Let $m$ be the largest length with $(q - 1)m < q d$. Partition $C$ by its values on $n - m$ coordinates; each of the at most $q^{n-m}$ parts is a code of length $m$ with distance at least $d$, to which the finite Plotkin bound applies, bounding it by $q d/(q d - (q - 1)m) \le q d$. Taking logarithms gives the finite bound, and dividing by $n_s$ the asymptotic one.

## Depends on

- [Minimum distance](../linear-codes/min-dist.md)

## Proof depends on

- [Plotkin bound](../bounds-on-code-size/plotkin-bound.md)

## Sources

- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
- M. Plotkin, "Binary Codes with Specified Minimum Distance", IRE Transactions on Information Theory, 1960.
