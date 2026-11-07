# Conjugacy of the Fibonacci and iccanobiF iterates of $b$

Let $\varrho_F'$ be the
iccanobiF substitution $a \mapsto ba$, $b \mapsto a$, extended to finite words by concatenation,
and for each $k$ let $g_k$ be the finite Fibonacci word $f_k$ with each $0$ written as $a$ and
each $1$ as $b$. For every $n \ge 1$,

$$ab\,g_{2n} = (\varrho_F')^{2n+1}(b)\,ba, \qquad ba\,g_{2n-1} = (\varrho_F')^{2n}(b)\,ab.$$

Since $g_k = \varrho_F^k(a) = \varrho_F^{k+1}(b)$ for the Fibonacci substitution $\varrho_F$
($a \mapsto ab$, $b \mapsto a$), this says $ab\,\varrho_F^{2n+1}(b) = (\varrho_F')^{2n+1}(b)\,ba$
and $ba\,\varrho_F^{2n}(b) = (\varrho_F')^{2n}(b)\,ab$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 52 (`jis-2025-25.1.5-prop-52`).
