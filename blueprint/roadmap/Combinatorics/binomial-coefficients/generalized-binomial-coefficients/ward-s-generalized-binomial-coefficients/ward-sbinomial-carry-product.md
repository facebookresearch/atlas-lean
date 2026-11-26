# Ward's identity for generalized binomial coefficients

Let
$s, f : \mathbb{N} \to \mathbb{Z}$ satisfy $s(b) \ne 0$ for every natural number $b$ and
$f(k) = \prod_{d \mid k} s(d)$ for every natural number $k$, the product running over the
positive divisors of $k$ (empty for $k = 0$). Write $f!(t) = \prod_{i=1}^{t} f(i)$. Then for all
natural numbers $n$ and $m$, the identity

$$\frac{f!(n+m)}{f!(n) \, f!(m)} =
\prod_{b=2}^{n+m} s(b)^{\lfloor ((n \bmod b) + (m \bmod b)) / b \rfloor}$$

holds in $\mathbb{Q}$.

The exponent $\lfloor ((n \bmod b) + (m \bmod b)) / b \rfloor$ is the carry in the ones position
when adding $n$ and $m$ in base $b$; for the classical case this recovers Kummer's carry-count
theorem.

## Sources

- Tom Edgar and Michael Z. Spivey, *Multiplicative Functions, Generalized Binomial Coefficients, and Generalized Catalan Numbers*, J. Integer Seq. 19 (2016), Article 16.1.6, Theorem 20 (Ward), equation (3), <https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.html>; attributed there to Morgan Ward.
