# Strong completeness of polynomial values plus reciprocals (Erdős Problem 351)

For every
polynomial $p$ with rational coefficients and positive leading coefficient, let $A_p$ be the set
of rational numbers $p(n) + 1/n$, where $n$ ranges over the positive integers. Then $A_p$ is
strongly complete: for every finite set $B$ of rational numbers there is an integer $N_0$ such
that every integer $m \ge N_0$ is the sum of the elements of some finite subset of
$A_p \setminus B$.

Resolved true: The maintained Erdős Problems page marks Problem 351 proved in the affirmative
and records that the positive solution follows from the positive solution of Problem 283.

## Sources

- plby/lean-proofs, src/latest/Util/PolynomialEgyptianSums.lean (theorem corollary_7_pos_leading, used by src/latest/ErdosProblems/Erdos351.lean), pinned revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Util/PolynomialEgyptianSums.lean#L10266. Moved from `OpenConjectures/NumberTheory/ErdosProblem351`.
