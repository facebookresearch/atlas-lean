# Attribute closure

Let $A$ be a finite set of attributes, $F$ a finite set of functional
dependencies over $A$ and $X \subseteq A$. The attribute closure $X^+$ of $X$ under $F$ is
computed by the closure algorithm: starting from $X$, repeat closure rounds (each adds the right
side of every dependency of $F$ whose left side is already included) until nothing changes, for
at most $|A|$ rounds.
