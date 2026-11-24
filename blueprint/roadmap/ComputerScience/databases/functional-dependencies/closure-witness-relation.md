# Closure witness relation

Let $A$ be a finite set of attributes, $F$ a finite set of
functional dependencies over $A$ and $X \subseteq A$. The closure witness relation for $X$ is the
relation with values in $\{\mathrm{true}, \mathrm{false}\}$ whose tuples are the tuple that is
$\mathrm{true}$ on every attribute and the tuple that is $\mathrm{true}$ exactly on the attribute
closure $X^+$ of $X$ under $F$. These two tuples agree exactly on $X^+$, and they coincide when
$X^+ = A$.
