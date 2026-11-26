# Sun's binomial-sum formula for generalized central trinomial coefficients

Let $T_n(b, c)$ be the coefficient of $x^n$ in $(x^2 + bx + c)^n$. For all integers $b, c$ and every natural number $n$,

$$T_n(b, c) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \binom{2k}{k} b^{\,n-2k} c^k = \sum_{k=0}^{n} \binom{n}{k} \binom{n-k}{k} b^{\,n-2k} c^k,$$

computed in the integers with $0^0 = 1$ (so for $b = 0$ and even $n$ only the term $k = n/2$ survives). In the second sum the exponent $n - 2k$ is truncated subtraction, read as $0$ when $2k > n$; those extra terms vanish, since then $n - k < k$ and $\binom{n-k}{k} = 0$. The two sums agree term by term for $2k \le n$, because $\binom{n}{k}\binom{n-k}{k} = \binom{n}{2k}\binom{2k}{k}$.

## Sources

- Zhi-Wei Sun, *Congruences involving generalized central trinomial coefficients*, Sci. China Math. 57 (2014), introduction.
- Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle Coefficients*, J. Integer Seq. 29 (2026), Article 26.5.2, Section 4.
