# Numbers with two comma-children

Fix a base $b \ge 2$, and say that $n$ has at least two
comma-children if there are distinct digits $y_1 \ne y_2$ below $b$ that are both comma
candidates for $n$ in base $b$ (distinct candidates $y$ give distinct children
$n + b\,(n \bmod b) + y$). Then a positive integer $n < b^2$ has at least two comma-children if
and only if $n = (b - 1 - 2x)\, b + x$ for some $x$ with $1 \le x$ and $2x \le b - 1$; and an
integer $n \ge b^2$ has at least two comma-children if and only if its base-$b$ representation,
most significant digit first, is $d\,(b-1) \cdots (b-1)\, d\,(b-1-d)$ with some number $i \ge 0$
of middle digits $b - 1$ and $1 \le d \le b - 2$.

## Sources

- Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci Quarterly 62 (2024), no. 3, Theorem 5.2 (`fq-2024-sloane05302024-thm-5.2`).
