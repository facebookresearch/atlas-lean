# Strong completeness of polynomial values plus reciprocals (Erdős Problem 351)

For every
polynomial $p$ with rational coefficients and positive leading coefficient, let $A_p$ be the set
of rational numbers $p(n) + 1/n$, where $n$ ranges over the positive integers. Then $A_p$ is
strongly complete: for every finite set $B$ of rational numbers there is an integer $N_0$ such
that every integer $m \ge N_0$ is the sum of the elements of some finite subset of
$A_p \setminus B$.

This answers Erdős Problem 351 in the affirmative; as Barreto noted, the positive answer follows
from the positive solution of Erdős Problem 283.

## Sources

- T. F. Bloom, Erdős Problem #283, https://www.erdosproblems.com/283 (positive solution; Barreto noted on the page for Problem #351 that it implies the statement above).
- T. F. Bloom, Erdős Problem #351, https://www.erdosproblems.com/351.
- plby/lean-proofs, https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Util/PolynomialEgyptianSums.lean#L10266.
