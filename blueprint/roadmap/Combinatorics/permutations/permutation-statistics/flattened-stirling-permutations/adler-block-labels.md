# Adler block labels

Let $n$ be a natural number and $P$ a set partition of the integer
interval $\{-n, \dots, n\}$; for $x$ in this interval write $P(x)$ for the block of $P$
containing $x$. The Adler block labels of $P$ are the integers $p$ with $1 \le p \le n$ such
that $p \le q$ for every positive $q \in P(p)$ and $p < -q$ for every negative $q \in P(p)$;
that is, $p$ is the least positive element of its block and is smaller than the absolute value
of every negative element of that block.

For a type $B$ set partition the block containing $0$ is never labelled, and from each pair of
blocks $\beta \ne -\beta$ exactly the block containing the element of least absolute value as a
positive element is labelled, by its least positive element; sorting the labels orders these
kept blocks as $\beta_1, \dots, \beta_m$.

## Sources

- Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3 (arXiv:2306.13034).
