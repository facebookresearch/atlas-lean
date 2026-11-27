# Occurs check: size bound

Let $x$ be a variable and $t$ a term in which $x$ occurs, with
$t$ not the variable $x$ itself. Then for every substitution $\sigma$, the term $\sigma(x)$ has
strictly smaller size than $t\sigma$, the result of applying $\sigma$ to $t$.

Consequently the equation $x = t$ has no unifier when $x$ occurs in $t$ and $t \ne x$ (the occurs
check).
