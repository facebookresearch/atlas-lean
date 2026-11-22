# BCNF violations

Let $F$ be a set of functional dependencies and $S$ a scheme, and write
$X^+$ for the attribute closure of a set $X$ of attributes under $F$. A set $X \subseteq S$
violates BCNF in $S$ when $S \not\subseteq X^+$ and $X^+ \cap S \not\subseteq X$, that is, when
the closure $X^+ \cap S$ of $X$ within $S$ is neither $X$ nor $S$.
