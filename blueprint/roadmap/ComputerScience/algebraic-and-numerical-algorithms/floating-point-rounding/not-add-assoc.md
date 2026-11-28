# Addition is not associative

Let $F$ be a binary format and $r$ a rounding mode. There are
values $a$, $b$ and $c$ of $F$ with $(a + b) + c \ne a + (b + c)$. For instance, with $M$ the
largest finite number, $(M + M) + (-M)$ is $+\infty$ when rounding to nearest or toward $+\infty$
and a zero when rounding toward zero or toward $-\infty$, as $M + M$ overflows, while
$M + (M + (-M)) = M$.

## Sources

- Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 3.2 (Ambiguity; Optimizers).
