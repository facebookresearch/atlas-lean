# Tseitin encoding invariant

Let $k$ be a natural number, let $r = (\ell, \Phi, k')$
consist of a literal $\ell$, a CNF formula $\Phi$ and a natural number $k'$, and let $v$ map
each assignment of Boolean values to the natural-number variables to a Boolean value. Call a
variable a gate in range if it equals $2j + 1$ for some $j$ with $k \le j < k'$. The invariant
holds for $k$, $r$ and $v$ when $k \le k'$; the variable of $\ell$ and every variable occurring
in a literal of $\Phi$ is even or a gate in range; every assignment $\sigma$ that satisfies
$\Phi$ gives $\ell$ the value $v(\sigma)$; and for every assignment $\sigma$ there is an
assignment $\tau$ that agrees with $\sigma$ on every variable that is not a gate in range,
satisfies $\Phi$ and gives $\ell$ the value $v(\sigma)$.

Here $r$ is meant to be the result (literal, clauses, next gate) of encoding a proposition with
gates numbered from $k$, and $v$ the value of that proposition.
