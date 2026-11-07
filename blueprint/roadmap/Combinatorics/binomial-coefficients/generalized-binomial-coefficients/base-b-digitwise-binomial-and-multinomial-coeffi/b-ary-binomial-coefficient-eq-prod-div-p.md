# Digit-product formula for $b$-ary binomial coefficients

Let $b \ge 2$ and let $n$, $k$
and $L$ be natural numbers with $n < b^L$ and $k < b^L$. Then the $b$-ary binomial coefficient
$\binom{n}{k}_b$ equals

$$\prod_{i=0}^{L-1} \binom{\lfloor n / b^i \rfloor \bmod b}{\lfloor k / b^i \rfloor \bmod b},$$

the product over the positions $i < L$ of the binomial coefficients of the $i$-th base-$b$ digits
of $n$ and $k$.
