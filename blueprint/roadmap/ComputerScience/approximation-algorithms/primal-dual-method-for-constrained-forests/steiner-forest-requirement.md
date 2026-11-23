# Steiner forest requirement

For demand pairs $(s_1, t_1), \ldots, (s_p, t_p)$, $f(S) = 1$ exactly when $S$ contains one
vertex of some pair but not the other. An edge set meets every cut with $f(S) = 1$ exactly when
it connects each $s_i$ to $t_i$ (the usual cut characterization of connectivity); its minimal
such sets are Steiner forests, called generalized Steiner trees by Goemans and Williamson. The
function is proper (symmetric by definition; a union of two sets separating no pair separates no
pair).
With a single pair this is the shortest path problem, and with all pairs from a terminal set
$T$ the Steiner tree problem (their Table 1).

## Background

- [Steiner tree](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/README.md):
  NP-completeness of the special case with one terminal set.

## Sources

- M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest problems", *SIAM J. Comput.* 24(2) (1995), 296–317 (journal version), §1, Table 1 and p. 297.
