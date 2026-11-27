# Near-optimal points round to optimal vertices

Let $A$, $b$, $c$ be integer data with measure $L$ as in [the encoding size page](encoding-size-of-a-linear-program.md), suppose $z = \min\{c^\top x : A x = b,\ x \ge 0\}$ is finite, and let $x$ be a feasible point with $c^\top x \le z + 2^{-2L}$. Then every vertex $x'$ of the feasible polyhedron with $c^\top x' \le c^\top x$ is an optimal solution.

## Depends on

- [Encoding size of a linear program](encoding-size-of-a-linear-program.md)

## Proof depends on

- [Objective values of distinct vertices are separated](objective-values-of-distinct-vertices-are-separated.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 13, Corollary 18, and Claim 20 for its use as a stopping rule.
