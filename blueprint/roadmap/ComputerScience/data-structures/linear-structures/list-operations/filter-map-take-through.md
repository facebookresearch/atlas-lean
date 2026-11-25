# Inclusive first-hit prefix commutes with filter-map

Let $s$ be a partial map from a type $A$ to a type $B$ (each element of $A$ has either a value
$s(x)$ or no value), let $p$ be a test that is true or false on each element of $B$, and let $L$
be a list of elements of $A$. For a list $M$ of elements of $A$, write $s^\ast(M)$ for the list of
the defined values $s(x)$, $x$ in $M$, in order. Call $x$ a hit when $s(x)$ is defined and $p(s(x))$
is true. Then $s^\ast$ of the inclusive first-hit prefix of $L$ for this hit test equals the
inclusive first-hit prefix of $s^\ast(L)$ for $p$.
