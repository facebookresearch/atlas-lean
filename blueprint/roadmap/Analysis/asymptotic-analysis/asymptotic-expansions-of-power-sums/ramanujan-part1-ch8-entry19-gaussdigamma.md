# Ramanujan's asymptotic expansion of a binomial combination of log-power sums

For natural
numbers $m$ and $x$ let $S_m(x) = \sum_{k=1}^{x} (\log k)^m$, let $c_m = (-1)^m \zeta^{(m)}(0)$,
where $\zeta^{(m)}(0)$ is the $m$-th derivative at $0$ of the real function
$s \mapsto \operatorname{Re} \zeta(s)$, and let $\psi_m(x) = S_m(x) - c_m$. Let $n$ be a natural
number. Then for every $m \le n$,

$$S_m(x) - \int_1^x (\log t)^m \, dt - \frac{(\log x)^m}{2} + (-1)^{m+1} m! \to c_m$$

as $x \to \infty$ through the natural numbers, and

$$\sum_{k=0}^{n} (-1)^{n+k} \binom{n}{k} (\log x)^k \psi_{n-k}(x) = n! \, x -
\frac{B_{n+1}}{(n+1) x^n} - \frac{n B_{n+2}}{2 (n+2) x^{n+1}} -
\frac{n (n + 5/3) B_{n+3}}{8 (n+3) x^{n+2}} + O\left(\frac{1}{x^{n+3}}\right)$$

as $x \to \infty$ through the natural numbers, where $B_j$ are the Bernoulli numbers with
$B_1 = -1/2$.

Proof: Analytic continuation of ζ to `re s > -1` by Euler–Maclaurin, Cauchy estimates for the
remainder's derivatives, and the Euler–Maclaurin tail expansion of the log-power sums.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
