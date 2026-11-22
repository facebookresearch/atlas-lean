# Ramanujan's binomial series transformation (Chapter 3, Entry 1, Corollary 1)

Let $n$ and
$x$ be complex numbers with $|x| < 1$, write $(n)_k = n(n-1)\cdots(n-k+1)$ for the falling
factorial (with $(n)_0 = 1$), and let $Q_0, Q_1, Q_2, \ldots$ be complex numbers such that, for
some $R > 0$, the power series $\sum_k Q_k z^k$ converges absolutely for every complex $z$ with
$|z| < R$. Suppose that the double series

$$\sum_{j, m \ge 0} \frac{Q_j\, (n)_{j+m}\, x^{j+m}}{m!}$$

is absolutely summable. Then the series

$$\sum_{k=0}^{\infty} \Bigl(\sum_{j=0}^{k} \frac{Q_j}{(k-j)!}\Bigr) (n)_k\, x^k$$

and

$$\sum_{k=0}^{\infty} Q_k\, (n)_k\, x^k\, (1 + x)^{n-k}$$

converge unconditionally to the same sum, where $(1 + x)^{n-k} = e^{(n-k) \log(1+x)}$ with the
principal branch of the logarithm.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 1, Corollary 1, printed p. 45 / PDF p. 55.
