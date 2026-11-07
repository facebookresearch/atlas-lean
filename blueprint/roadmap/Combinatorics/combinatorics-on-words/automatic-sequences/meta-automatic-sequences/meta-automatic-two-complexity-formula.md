# Factor complexity of $\mathcal{M}_2$

Let $p(n)$ be the factor complexity of the
meta-automatic sequence $\mathcal{M}_2$. Then $p(1) = 2$, and for every $n \ge 2$, writing
$k = \lfloor \log_2 n \rfloor$ (so that $2^k \le n < 2^{k+1}$), the following hold.
If $k \equiv 0 \pmod 3$, then $p(n) = 2n + 2^{k-1} - 2$ when $n \le 2^k + 1$,
$p(n) = 4n - (3 \cdot 2^{k-1} + 4)$ when $2^k + 1 \le n \le 7 \cdot 2^{k-2} + 1$, and
$p(n) = 2n + 2^{k+1} - 2$ when $n \ge 7 \cdot 2^{k-2} + 1$.
If $k \equiv 1 \pmod 3$, then $p(n) = 2n + 2^k - 2$ when $n \le 2^k + 1$,
$p(n) = 4n - (2^k + 4)$ when $2^k + 1 \le n \le 3 \cdot 2^{k-1} + 1$, and
$p(n) = 2n + 2^{k+1} - 2$ when $n \ge 3 \cdot 2^{k-1} + 1$.
If $k \equiv 2 \pmod 3$, then $p(n) = 2n + 2^k - 2$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Proposition 37 (`jis-2026-26.4.1-prop-37`).
