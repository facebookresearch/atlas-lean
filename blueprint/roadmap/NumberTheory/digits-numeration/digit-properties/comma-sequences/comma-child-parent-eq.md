# Recovering the parent of a comma-child

Fix a base $b \ge 2$ and a natural number $n$.
Call $n$ a comma-child of $k$ if $n = k + b\,(k \bmod b) + y$ for some comma candidate digit $y$
of $k$ in base $b$. Let $f$ be the most significant base-$b$ digit of $n$ and let
$x = (n - f) \bmod b$. If $n$ is a comma-child of a positive integer $k$, then
$k = n - x b - f$; and if the integer $n - x b - f$ is negative, then $n$ is not a comma-child
of any positive integer.

## Sources

- Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci Quarterly 62 (2024), no. 3, Lemma 5.3.
