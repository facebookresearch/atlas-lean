# The closure algorithm computes the attribute closure

Let $F$ be a finite set of
functional dependencies over a finite set of attributes and $X$ a set of attributes. An
attribute $a$ lies in the attribute closure $X^+$ of $X$ under $F$, as computed by the closure
algorithm, if and only if the dependency $X \to \{a\}$ is derivable from $F$ with Armstrong's
axioms.
