# Domination signature

Let $R$ be a simple graph on a vertex set $V$ (the row). A map
$\sigma$ assigning to each vertex of $V$ a domination state (uncovered, covered or occupied) is a
signature for $R$ if no uncovered vertex is adjacent in $R$ to an occupied vertex: for all
vertices $i, j$ adjacent in $R$, it is not the case that $\sigma(i)$ is uncovered and $\sigma(j)$
is occupied.

When $R$ is the path on $m$ vertices, signatures are the strings of length $m$ in which no
uncovered entry is next to an occupied one; when $R$ is the cycle on $m$ vertices the condition
also applies to the first and last entries (the paper's cyclic signatures).

## Sources

- Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3.
