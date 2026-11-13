# Trinomial coefficients along lines from a square-root series

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and
$[t^m]\,F$ for the coefficient of $t^m$ in a formal power series $F$ over $\mathbb{Q}$. Let $S$
be a power series over $\mathbb{Q}$ with $S^2 = 1 - 2t - 3t^2$ and $S(0) = 1$. For natural
numbers $n, a, b, k$ with $2a \le b$,
$2^{(b-a)k} \binom{n+ak}{n+bk}_2 = [t^{n+bk}]\, S^{-1} (1 - t - S)^{(b-a)k}$.

Equivalently $\binom{n+ak}{n+bk}_2 = [t^n]\, S^{-1}
\left((1 - t - S)^{b-a} / (2^{b-a} t^b)\right)^k$, the paper's form, which allows integers
$a$ and $b$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 38 (`jis-2025-25.3.5-thm-38`).
