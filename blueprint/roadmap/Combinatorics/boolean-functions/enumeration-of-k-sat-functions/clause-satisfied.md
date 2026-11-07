# Satisfied clause

Let $n \in \mathbb{N}$. A clause on $n$ variables is a finite set $C$ of
literals $(i, b)$, where $i \in \{0, \dots, n - 1\}$ is a variable and $b \in \{\mathrm{true},
\mathrm{false}\}$. An assignment $x : \{0, \dots, n - 1\} \to \{\mathrm{true}, \mathrm{false}\}$
satisfies $C$ if $x_i = b$ for some literal $(i, b) \in C$.

## Sources

- [OWR-10252930-018], `k`-SAT clause semantics.
