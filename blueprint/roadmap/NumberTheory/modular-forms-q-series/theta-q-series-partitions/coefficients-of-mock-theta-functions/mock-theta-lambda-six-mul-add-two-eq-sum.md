# Coefficients of the mock theta function $\lambda$ at indices $6n+2$

Write
$\lambda(q) = \sum_{n \ge 0} P_\lambda(n) q^n$ for the sixth-order mock theta function $\lambda$,
let $f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $\overline{p}_3(j)$ be the coefficient of
$q^j$ in $(f_2/f_1^2)^3$. Then for every $n \ge 0$,

$$
P_\lambda(6n+2) = 3 \sum_{m \ge 0,\ 3m(m+1)/2 \le n} (-1)^m (2m+1)\,
\overline{p}_3\bigl(n - 3m(m+1)/2\bigr) +
6 \sum_{m \ge 0} \sum_{k \ge 1,\ 3k^2 + 3m(m+1)/2 \le n} (-1)^{m+k} (2m+1)\,
\overline{p}_3\bigl(n - 3k^2 - 3m(m+1)/2\bigr).
$$

## Sources

- Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 9 (`integers-2025-A72-thm-9`).
