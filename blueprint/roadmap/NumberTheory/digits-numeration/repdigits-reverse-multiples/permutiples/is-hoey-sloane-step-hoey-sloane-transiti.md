# Hoey-Sloane transitions are transitions of the machine

Let $1 < n < b$, let
$e = (d_1, d_2)$ be an edge of the $(n, b)$-mother graph, and let $(c_1, c_2)$ be the Hoey-Sloane
transition of $e$, that is, $c_1 = \lambda(d_1 + (b - n) d_2)$ and $c_2 = (n d_2 - d_1 + c_1) / b$,
where $\lambda$ is the least non-negative residue modulo $b$. Then the input $e$ moves state $c_1$
to state $c_2$ in one transition of the $(n, b)$-Hoey-Sloane machine.

By the uniqueness of Hoey-Sloane transitions (Theorem 5), it is the only transition labelled
by $e$.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Definition 6, from Theorems 5 and 6.
