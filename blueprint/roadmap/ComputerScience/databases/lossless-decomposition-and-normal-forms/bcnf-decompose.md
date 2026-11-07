# BCNF decomposition with bounded depth

Let $F$ be a set of functional dependencies, $l$ a
list of attributes, $n$ a natural number and $S$ a scheme. For $n = 0$ the result is the list $[S]$.
For $n > 0$, the candidate violations of BCNF in $S$ built from $l$ are searched in order for the
first $X$ that violates BCNF in $S$ for $F$. If there is none, the result is $[S]$. Otherwise, with
$X^+$ the attribute closure of $X$ under $F$, the result is the decomposition of $X^+ \cap S$
followed by the decomposition of $S \setminus (X^+ \setminus X)$, both computed with depth bound
$n - 1$.
