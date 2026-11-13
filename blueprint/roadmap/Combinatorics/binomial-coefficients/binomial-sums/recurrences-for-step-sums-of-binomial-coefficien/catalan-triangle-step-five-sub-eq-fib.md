# Alternating step-five sums of Catalan's triangle are Fibonacci numbers

For natural
numbers $n$ and $k$ let $d(n, k) = \frac{k + 1}{n + 1} \binom{2(n + 1)}{n - k}$ if $k \le n$,
and $d(n, k) = 0$ if $k > n$. Let $F_m$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then
for every $n \in \mathbb{N}$,
$\sum_{j=0}^{n} \bigl(d(n, 5j + 1) - d(n, 5j + 2)\bigr) = F_{2n}$ and
$\sum_{j=0}^{n} \bigl(d(n, 5j) - d(n, 5j + 3)\bigr) = F_{2n+1}$.

The numbers $d(n, k)$ form Catalan's triangle (OEIS A039598), the Riordan array $(g, xg)$ with
$g(x) = (1 - 2x - \sqrt{1 - 4x})/(2x^2)$; since $d(n, m) = 0$ for $m > n$, the sums are the full
sums over all $j \ge 0$.

## Sources

- Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 13.
