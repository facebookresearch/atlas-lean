# Termination of linear loops over the reals is decidable

For rational matrices $A$ ($N \times N$) and $B$ ($M \times N$) and rational vectors $b$ and $c$, it is decidable whether the loop

$$\mathbf{while}\ (Bx > b)\ \{\, x := Ax + c \,\}$$

terminates from every initial value $x \in \mathbb{R}^N$. The homogeneous case $b = 0$, $c = 0$ is decided by inspecting the real eigenvectors of $A$ for positive eigenvalues: if none satisfies $Bv \ge 0$ the loop terminates, and otherwise the loop is reduced, through the real Jordan form of $A$, to one over the generalized eigenspaces of positive eigenvalues, whose termination is decided by a nondeterministic procedure that guesses, for each loop inequality, which term dominates eventually and checks a formula of real arithmetic. The general case reduces to the homogeneous one by adding a variable.

## Expansion

This page becomes ready once these prerequisites are stated:

- The real Jordan form of a real matrix (proof prerequisite)
- Tiwari's reduction to the generalized eigenspaces of positive eigenvalues and the correctness of the dominant-term procedure (proof prerequisite)

## Proof depends on

- [Eigenvector witness for nonterminating linear loops](eigenvector-witness-for-nonterminating-linear-loops.md)
- [Quantifier elimination preserves truth](../../../../Logic/model-theory/quantifier-elimination-for-real-closed-fields/holds-qe.md)

## Sources

- A. Tiwari, "Termination of linear programs", *Computer Aided Verification (CAV 2004)*, LNCS 3114, Springer, 2004, pp. 70–82, author copy <https://www.csl.sri.com/users/tiwari/papers/cav04.pdf>, Section 3, Lemma 1; Section 4, Lemma 2 and Theorem 4 (homogeneous case); Section 5, Theorem 5 (general case).
