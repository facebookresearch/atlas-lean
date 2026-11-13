# Euler–Lucas multinomial expansion of $(x + q/2)^m$

Let $E_k$ be the Euler (secant)
numbers, with exponential generating function $2/(e^t + e^{-t})$, and let $L_k$ be the Lucas
numbers ($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$). For all natural numbers $q \ge 1$ and
$m$ and every real number $x$,

$$2^q \left(x + \frac{q}{2}\right)^m = \sum_{n=0}^{m} \binom{m}{n} x^{m-n}
\sum_{j_1 + \dots + j_q + \ell_1 + \dots + \ell_q = n} \left(\frac{\sqrt{5}}{2}\right)^{\ell_1 +
\dots + \ell_q} \frac{n!}{j_1! \cdots j_q! \, \ell_1! \cdots \ell_q!} E_{\ell_1} \cdots
E_{\ell_q} L_{j_1} \cdots L_{j_q},$$

where the inner sum runs over all tuples $(j_1, \dots, j_q, \ell_1, \dots, \ell_q)$ of natural
numbers with sum $n$.

The coefficient is the full multinomial coefficient; the paper's displayed definition omits the
factors $\ell_i!$.

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Theorem 18.
