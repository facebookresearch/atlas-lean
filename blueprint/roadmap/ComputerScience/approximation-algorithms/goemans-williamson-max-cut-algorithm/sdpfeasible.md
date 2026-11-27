# Feasible matrices of the MAX CUT semidefinite program

A matrix $Y$ is feasible when it is positive semidefinite and $Y_{ii} = 1$ for every vertex $i$.
The semidefinite program maximizes the [objective](sdp-objective.md) over these matrices; its
value is the relaxation bound $\mathrm{SDP}$ of the survey.

## Background

- [Theta function of a graph](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/README.md):
  the theta body of Grötschel, Lovász and Schrijver is defined by the same kind of positive
  semidefinite constraint.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §4.
- M. X. Goemans, "Semidefinite programming in combinatorial optimization", *Math. Programming* 79 (1997), 143–161 (author's PDF), §5, program (11).
