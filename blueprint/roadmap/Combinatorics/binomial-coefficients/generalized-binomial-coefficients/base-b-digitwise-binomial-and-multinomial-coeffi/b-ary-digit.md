# Base-$b$ digit of a natural number

For natural numbers $b$, $n$ and $l$, the rank-$l$
base-$b$ digit $n_l$ of $n$ is the entry at position $l$ (counting from $0$) of the list of
base-$b$ digits of $n$, least significant digit first, and $0$ when $l$ is at least the length of
that list (with $0$ having no digits). For $b \ge 2$ this is the coefficient of $b^l$ in the
base-$b$ expansion of $n$.

For $b \le 1$ the digit list follows Mathlib's convention: for $b = 0$ a positive $n$ has the
single digit $n$, and for $b = 1$ the digits of $n$ are $n$ ones.

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex, lines 349-359.
