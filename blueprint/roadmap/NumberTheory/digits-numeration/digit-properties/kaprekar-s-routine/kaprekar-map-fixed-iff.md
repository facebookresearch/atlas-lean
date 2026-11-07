# Classification of decimal Kaprekar numbers

Let $n \ge 3$ and $0 < \alpha < 10^n$. Then
the Kaprekar map on $n$-digit strings fixes $\alpha$ if and only if $\alpha$ is the Kaprekar
difference of some string $s$ of exactly $n$ decimal digits of one of the following five forms,
where juxtaposition is concatenation, $(w)^k$ is the block $w$ repeated $k$ times, and in each
form the exponents are chosen independently with $x, x_1, x_2 \ge 1$ and $y, y_1, y_2 \ge 0$:
$(495)^x$; $6174\,(36)^y$; $(123456789)^x (36)^y$;
$(123456789)^{x_1} (36)^{x_2} (495)^{2x_2} (27)^{3x_2}$;
$(124578)^{x_1} (09)^{x_2} (123456789)^{y_1} (36)^{y_2}$.

The witness string must have length $n$: $495$ is the Kaprekar difference of $(495)^1$, but the
Kaprekar map on $4$-digit strings sends $495$ to $9081$.

## Sources

- Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly 62 (2024), Article iwasaki06162024-ASrev2, Theorem 3.1.
