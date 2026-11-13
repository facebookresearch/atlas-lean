# Multinomial Bernoulli–Fibonacci expansion of $(x + q\beta)^m$

Let
$\beta = (1 - \sqrt{5})/2$, let $B_k$ be the Bernoulli numbers with $B_1 = -1/2$, and let $F_k$ be
the Fibonacci numbers. For every natural number $q \ge 1$, every natural number $m$ and every real
number $x$, the power $(x + q\beta)^m$ equals the sum, over $0 \le n \le m$ and over all pairs of
tuples of natural numbers $(j_1, \dots, j_q)$ and $(\ell_1, \dots, \ell_q)$ with
$j_1 + \dots + j_q + \ell_1 + \dots + \ell_q = n$, of

$$
\sqrt{5}^{\,\ell_1 + \dots + \ell_q} \frac{n!}{j_1! \cdots j_q! \, \ell_1! \cdots \ell_q!}
\binom{m}{n} B_{\ell_1} \cdots B_{\ell_q} \frac{F_{j_1+1}}{j_1+1} \cdots \frac{F_{j_q+1}}{j_q+1}
x^{m-n}.
$$

The coefficient is the full multinomial coefficient: the paper's displayed definition omits the
factors $\ell_i!$, and with them omitted the identity fails, for example at $q = 2$,
$x = \sqrt{5}$, $m = 2$.

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Theorem 15.
