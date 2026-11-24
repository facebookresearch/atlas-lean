# Turán graphs are $r$-colourable

For $r \ge 1$, the Turán graph $T(n, r)$ on $\{0, \dots, n-1\}$ is properly coloured by $v \mapsto v \bmod r$. In $T(n, r)$, two vertices are adjacent exactly when their residues mod $r$ differ, so each residue class is independent. These classes are the $r$ parts of the complete $r$-partite graph $T(n, r)$.

## Sources

- P. Turán, "On an extremal problem in graph theory" (in Hungarian), *Mat. Fiz. Lapok* 48 (1941), 436–452 (not consulted directly); the definition is Mathlib's `SimpleGraph.turanGraph`.
