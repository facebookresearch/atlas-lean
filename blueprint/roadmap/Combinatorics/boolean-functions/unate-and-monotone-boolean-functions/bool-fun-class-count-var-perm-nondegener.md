# Non-degenerate permutation classes as a difference

Let $(P_n)_{n \ge 0}$ be a family of
properties, $P_n$ a property of $n$-variable Boolean functions, that is invariant under renaming
variables: for all $m$ and $n$, every injection $e$ from $\{1, \dots, m\}$ to $\{1, \dots, n\}$
and every $m$-variable function $g$, the $n$-variable function $x \mapsto g(x \circ e)$ has $P_n$
if and only if $g$ has $P_m$. Write $[P]_n$ for the number of classes of $n$-variable functions
with $P_n$ under permutation of the variables, and $\mathrm{nd}[P]_n$ for the same count over the
non-degenerate $n$-variable functions with $P_n$. Then for every $n$,

$$\mathrm{nd}[P]_{n+1} = [P]_{n+1} - [P]_n,$$

where the subtraction is truncated at $0$; this is the paper's
$\mathrm{nd}[P]_n = [P]_n - [P]_{n-1}$ for $n \ge 1$.

The paper assumes only closure under permutations of the variables, which is not enough; see the
summation form of Proposition 11.

## Sources

- Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer Sequences 28 (2025), Article 25.3.4, Proposition 11 (`jis-2025-25.3.4-prop-11`).
