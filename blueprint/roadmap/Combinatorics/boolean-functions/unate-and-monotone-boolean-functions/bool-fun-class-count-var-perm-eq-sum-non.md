# Permutation classes counted by non-degenerate ones

Let $(P_n)_{n \ge 0}$ be a family of
properties, $P_n$ a property of $n$-variable Boolean functions, that is invariant under renaming
variables: for all $m$ and $n$, every injection $e$ from $\{1, \dots, m\}$ to $\{1, \dots, n\}$
and every $m$-variable function $g$, the $n$-variable function $x \mapsto g(x \circ e)$ has $P_n$
if and only if $g$ has $P_m$. Write $[P]_n$ for the number of classes of $n$-variable functions
with $P_n$ under permutation of the variables, and $\mathrm{nd}[P]_n$ for the same count over the
non-degenerate $n$-variable functions with $P_n$. Then for every $n$,

$$[P]_n = \sum_{i=0}^{n} \mathrm{nd}[P]_i.$$

The paper assumes only closure under permutations of the variables; the counting argument also
needs invariance under adding or removing dummy variables. Closure under permutations alone is not
enough: if $P_1$ holds for all four $1$-variable functions and $P_n$ holds for none when
$n \ne 1$, then $[P]_1 = 4$ but $\mathrm{nd}[P]_0 + \mathrm{nd}[P]_1 = 0 + 2 = 2$.

## Sources

- Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer Sequences 28 (2025), Article 25.3.4, Proposition 11 (`jis-2025-25.3.4-prop-11`).
