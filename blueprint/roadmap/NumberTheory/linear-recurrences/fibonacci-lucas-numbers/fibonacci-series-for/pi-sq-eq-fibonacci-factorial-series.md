# Fibonacci series for $\pi^2$ with polynomial weights

Let $p_1, p_2, \dots$ be polynomials
with integer coefficients such that $p_1 = 1$ and, for every $n \ge 1$,
$p_{n+1}(x) = (2x + 2n + 1)(2x + 2n + 2)\, p_n(x) - (x + 1)^2 p_n(x + 1)$. Let $(a_n)_{n \ge 0}$
be real numbers with $a_0 = -8\sqrt{5}/250$, $a_1 = (25 - 4\sqrt{5})/250$ and
$a_{n+1} = a_n + a_{n-1}$ for $n \ge 1$, and let $(b_n)_{n \ge 0}$ be real numbers with
$b_0 = b_1 = 0$ and $b_{n+1} = b_n + b_{n-1} + (-1)^{n+1} p_n(0)/(2n)!$ for $n \ge 1$. Write $F_m$
for the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every $n \ge 1$,

$$\pi^2 = \frac{1}{a_{n-1}} \Bigl(b_{n-1} + (-1)^n \sum_{k=0}^{\infty}
\frac{(k!)^2 \, p_n(k) \, F_{2k+2}}{(2k+2n)!}\Bigr)$$

and

$$\pi^2 = \frac{1}{a_n} \Bigl(b_n + (-1)^{n+1} \sum_{k=0}^{\infty}
\frac{(k!)^2 \, p_n(k) \, F_{2k+1}}{(2k+2n)!}\Bigr).$$

## Sources

- Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1, Theorem 2.1 (`fq-2024-tonien10292023-thm-2.1`).
