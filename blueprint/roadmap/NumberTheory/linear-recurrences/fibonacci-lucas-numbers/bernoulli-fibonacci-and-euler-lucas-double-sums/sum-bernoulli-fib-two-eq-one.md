# A multinomial sum of Bernoulli and Fibonacci numbers equal to one

Let $F_n$ be the
Fibonacci numbers and let $B_k$ be the Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every
natural number $m$,

$$\sum_{n=0}^{m} \sum_{j_1 + j_2 + \ell_1 + \ell_2 = n} \sqrt{5}^{\,\ell_1 + \ell_2 + m - n}
\frac{n!}{j_1!\, j_2!\, \ell_1!\, \ell_2!} \binom{m}{n} B_{\ell_1} B_{\ell_2}
\frac{F_{j_1+1}}{j_1+1} \cdot \frac{F_{j_2+1}}{j_2+1} = 1,$$

where the inner sum runs over all quadruples $(j_1, j_2, \ell_1, \ell_2)$ of natural numbers with
sum $n$.

This is the case $q = 2$, $x = \sqrt{5}$ of Theorem 15, since $\sqrt{5} + 2\beta = 1$ for
$\beta = (1 - \sqrt{5})/2$. The paper's displayed multinomial coefficient omits the factors
$\ell_1!\, \ell_2!$; with that coefficient the sum at $m = 2$ is $8/3$, not $1$.

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Corollary 17.
