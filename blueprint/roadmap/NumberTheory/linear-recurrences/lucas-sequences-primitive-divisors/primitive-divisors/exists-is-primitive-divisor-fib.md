# Primitive divisors of Fibonacci numbers

Write $F_j$ for the $j$-th Fibonacci number.
For every natural number $n \ge 7$ with $n \ne 12$, $F_n$ has a primitive divisor with respect
to the discriminant $5$: there is a prime $p$ that divides $F_n$ but does not divide
$5 F_1 F_2 \cdots F_{n-1}$.

This is the Fibonacci case of Carmichael's theorem on Lucas sequences, with
$\alpha = (1 + \sqrt{5})/2$ and $\beta = (1 - \sqrt{5})/2$, so that $(\alpha - \beta)^2 = 5$.

## Sources

- Haojie Hong, *On big primitive divisors of Fibonacci numbers*, arXiv:2312.04354v1, `bigPFn.tex` lines 153–158 (<https://arxiv.org/abs/2312.04354>); R. D. Carmichael, *On the numerical factors of the arithmetic forms αⁿ±βⁿ*, Ann. of Math. (2) 15 (1913), 30–70.
