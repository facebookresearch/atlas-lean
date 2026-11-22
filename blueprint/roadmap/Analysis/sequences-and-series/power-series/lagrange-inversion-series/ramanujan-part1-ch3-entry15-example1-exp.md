# Ramanujan's exponential series for powers of two

Let $m$ and $n$ be real numbers with
$0 < n \le 2$. Then the series

$$1 + \sum_{k=1}^{\infty} \frac{m}{2^{k n} \, k!} \prod_{j=1}^{k-1} (m + k n - j)$$

converges unconditionally to $2^m$.

Proof: Following Berndt and the generalized binomial series of Graham, Knuth, and Patashnik,
the series is realized as $B_n(z)^m$, where $B_n = 1 + z B_n^n$; root selection at
$z = 2^{-n}$, with the endpoint supplied by Entry 14's Catalan-power series, gives $B_n = 2$.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 15, Example 1, printed pp. 73-75 / PDF pp. 83-85.
