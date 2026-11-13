# Multinomial Genocchi–Lucas expansion of $(x + q\beta)^m$

Let
$\beta = (1 - \sqrt{5})/2$, let $G_k$ be the Genocchi numbers and $L_k$ the Lucas numbers, and for
every natural number $n$ let

$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}
$$

be the Genocchi–Lucas coefficient. Then for every natural number $q \ge 1$, every natural number
$m$ and every real number $x$,

$$
(2\sqrt{5})^q (x + q\beta)^m = \sum_{n=0}^{m} \binom{m}{n} x^{m-n}
\sum_{j_1 + \dots + j_q = n} \frac{n!}{j_1! \cdots j_q!} c_{j_1} \cdots c_{j_q},
$$

where the inner sum runs over all $q$-tuples $(j_1, \dots, j_q)$ of natural numbers with
$j_1 + \dots + j_q = n$.

This is the $q$-fold convolution form of the corrected Theorem 11, the Genocchi–Lucas expansion
of $(x + \beta)^m$. As printed, with factors $L_{n-j_i+1}/(n-j_i+1)$, the paper's displayed
multinomial coefficient and no correction terms, the identity fails already at $q = 1$.

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Theorem 20.
