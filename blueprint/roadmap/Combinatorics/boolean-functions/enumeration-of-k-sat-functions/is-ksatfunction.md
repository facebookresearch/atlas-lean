# $k$-SAT function

Let $k, n \in \mathbb{N}$. A Boolean function
$f : \{\mathrm{true}, \mathrm{false}\}^n \to \{\mathrm{true}, \mathrm{false}\}$ is a $k$-SAT
function on $n$ variables if there is a finite set $S$ of clauses on $n$ variables such that each
clause in $S$ has at most $k$ literals, no two of them on the same variable, and for every
assignment $x$, $f(x) = \mathrm{true}$ if and only if $x$ satisfies every clause in $S$.

## Sources

- [OWR-10252930-018], `k`-SAT functions.
