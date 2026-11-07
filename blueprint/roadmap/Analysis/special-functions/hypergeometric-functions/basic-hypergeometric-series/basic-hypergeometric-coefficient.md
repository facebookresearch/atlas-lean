# Coefficients of the basic hypergeometric series

Let $r$ and $s$ be natural numbers, let
$a_1, \dots, a_r$, $b_1, \dots, b_s$ and $q$ be complex numbers, and write
$(x;q)_n = \prod_{j=0}^{n-1} (1 - x q^j)$ for the finite $q$-Pochhammer symbol, so that
$(q;q)_n = \prod_{j=0}^{n-1} (1 - q^{j+1})$. For a natural number $n$, the coefficient of $z^n$ in
the basic hypergeometric series ${}_r\phi_s(a_1, \dots, a_r; b_1, \dots, b_s; q, z)$ is

$$\frac{(a_1;q)_n \cdots (a_r;q)_n}{(q;q)_n\,(b_1;q)_n \cdots (b_s;q)_n}
\left((-1)^n q^{\binom{n}{2}}\right)^{1+s-r},$$

where the exponent $1 + s - r$ is an integer and may be negative. This is DLMF 17.4.1, which is
written for $r + 1$ upper parameters, restated for $r$ upper parameters.

No condition on the parameters is imposed: division by zero gives $0$, and so does every negative
power of $0$. Analytic applications must separately establish that the denominator does not
vanish.
