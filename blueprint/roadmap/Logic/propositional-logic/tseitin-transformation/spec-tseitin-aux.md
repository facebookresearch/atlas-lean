# Correctness invariant of the Tseitin encoding

Let $\iota$ map atoms to natural numbers,
let $A$ be a proposition and $k$ a natural number, and let $(\ell, \Phi, k')$ be the reference
Tseitin encoding of $A$ with gates numbered from $k$: the literal naming $A$, its defining
clauses and the next unused gate number. For an assignment $\sigma$ of Boolean values to the
natural-number variables, let $A[\sigma]$ be the truth value of $A$ when each atom $a$ gets
the value $\sigma(2\iota(a))$, and call a variable a gate in range if it equals $2j + 1$ for
some $j$ with $k \le j < k'$. Then $k \le k'$; the variable of $\ell$ and every variable
occurring in a literal of $\Phi$ is even or a gate in range; every assignment $\sigma$ that
satisfies $\Phi$ gives $\ell$ the value $A[\sigma]$; and for every assignment $\sigma$ there is
an assignment $\tau$ that agrees with $\sigma$ on every variable that is not a gate in range,
satisfies $\Phi$ and gives $\ell$ the value $A[\sigma]$.
