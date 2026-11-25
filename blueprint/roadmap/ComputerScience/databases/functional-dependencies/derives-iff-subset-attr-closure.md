# The closure algorithm decides derivability

Let $A$ be a finite set of attributes, $F$ a
finite set of functional dependencies over $A$ and $X, Y \subseteq A$. Then $X \to Y$ is
derivable from $F$ with Armstrong's axioms if and only if $Y \subseteq X^+$, where $X^+$ is the
attribute closure of $X$ under $F$ computed by the closure algorithm.
