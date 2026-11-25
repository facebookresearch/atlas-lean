# Correctness of naive string matching

Let $\alpha$ be a type whose Boolean equality
agrees with equality, and write $|t|$ for the length of a list $t$. For every pattern $p$ and
text $t$ over $\alpha$ and every natural number $s$, the naive matcher run on $p$ and $t$
reports the shift $s$ if and only if $p$ matches $t$ at $s$, that is, $s \le |t|$ and $p$ is a
prefix of the suffix of $t$ obtained by dropping its first $s$ symbols.

In particular, the empty pattern is reported at every shift $s \le |t|$.
