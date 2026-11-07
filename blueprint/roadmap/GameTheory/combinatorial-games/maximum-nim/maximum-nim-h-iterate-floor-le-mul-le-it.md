# Logarithmic bounds on the iterates of h_k

Let $k \ge 2$ and $n \ge 1$ be natural numbers,
let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ on natural numbers, write $h_k^p$ for its $p$-fold
iterate, and let

$$v = \frac{\log n}{\log k - \log(k-1)}, \qquad w = \frac{\log(n+1) - \log 2}{\log k - \log(k-1)},$$

where $\log$ is the natural logarithm. Then

$$h_k^{\lfloor w \rfloor}(k-1) \le n(k-1) \le h_k^{\lceil v \rceil}(k-1).$$

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Lemma 8.
