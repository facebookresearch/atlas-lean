# Zurita's series $\sum_{k > n} 4^k x^k / ((k - n)\binom{2k}{k})$

Let $n \ge 1$, let
$S_n(x) = \sum_{k=0}^n s_k x^k$ and $T_{n-2}$ be Zurita's polynomials (with $T_{-1} = 0$), and
let $x$ be real with $0 < x < 1$. Then

$$
\sum_{k > n} \frac{4^k x^k}{(k - n)\binom{2k}{k}} = x\, T_{n-2}(x) +
\sqrt{\frac{x}{1 - x}}\, \arcsin(\sqrt{x})\, S_n(x) +
\sum_{k=0}^{n-1} \Bigl(1 - \frac{4^k}{\binom{2k}{k}}\Bigr) \frac{x^k}{k - n} -
\Bigl(\frac12 \sum_{k=1}^{n} \frac{4^k s_{n-k}}{k \binom{2k}{k}}\Bigr) x^n.
$$

The source prints the range $|x| < 4$. The statement here is restricted to $0 < x < 1$, inside
the range $|x| < 1$ that the source's Theorem 1 gives in this case; since
$\binom{2k}{k} \le 4^k$, the series diverges for $x \ge 1$.

## Sources

- Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 1 (`integers-2026-A2-cor-1`).
