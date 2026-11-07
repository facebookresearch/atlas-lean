# Hadamard product of two Fibonacci-type series

Let $R$ be a commutative ring, let
$a, b \in R$, and let $n \ge 2$ be a natural number. For each $k$, let $f_k$ be the coefficient of
$x^k$ in $1/(1 - ax - x^2)$ and $g_k$ the coefficient of $x^k$ in $1/(1 - bx - x^n)$, the
inverses taken in $R[[x]]$. Then the Hadamard product $\sum_{k \ge 0} f_k g_k x^k$ equals

$$
\frac{1 - f_{n-2}\, x^n}{1 - ab\, x - b^2 x^2 - (f_n + f_{n-2})\, x^n -
(2b f_{n-1} - ab f_{n-2})\, x^{n+1} + (-1)^n x^{2n}}
$$

in $R[[x]]$, where the denominator has constant coefficient $1$ and so is invertible.

## Sources

- Jong Hyun Kim, "Hadamard Products and Tilings", Journal of Integer Sequences 12 (2009), Article 09.7.4, Theorem `eq:61`, lines 430-437, <https://cs.uwaterloo.ca/journals/JIS/VOL12/Kim/kim18.tex>. Proves `Wanted` entry `hadamard_fibonacci_product`.
