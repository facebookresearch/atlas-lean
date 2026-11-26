# Multiplication is not associative

Let $F$ be a binary format with $q_{\min} \le -1$ and
$q_{\max} \ge 1$, as for binary32 and binary64, and let $r$ be a rounding mode. There are values
$a$, $b$ and $c$ of $F$ with $(a \times b) \times c \ne a \times (b \times c)$. For
instance, with $M$ the largest finite number, $(M \times 2) \times \frac{1}{2}$ is $+\infty$ when
rounding to nearest or toward $+\infty$ and $M / 2$ when rounding toward zero or toward
$-\infty$, as $M \times 2$ overflows, while $M \times (2 \times \frac{1}{2}) = M$.
