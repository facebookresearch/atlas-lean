# Generating sum of the upper half of a trinomial row

Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For every natural number $n$
and every complex number $w$,

$$\sum_{k=0}^{n} \binom{n}{n-k}_2 w^{n+k} = \frac{(1+w+w^2)^n}{2} + \frac{\binom{n}{n}_2 w^n}{2} +
\frac{w^2-1}{2} \sum_{k=0}^{n-1} \binom{k}{k}_2 (1+w+w^2)^{n-1-k} w^k.$$

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 40 (`jis-2025-25.3.5-cor-40`).
