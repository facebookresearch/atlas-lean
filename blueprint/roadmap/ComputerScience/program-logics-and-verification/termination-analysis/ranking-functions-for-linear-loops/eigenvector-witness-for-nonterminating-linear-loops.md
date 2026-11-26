# Eigenvector witness for nonterminating linear loops

Let $A$ be a real $N \times N$ matrix and $B$ a real $M \times N$ matrix, and consider the homogeneous linear loop

$$\mathbf{while}\ (Bx > 0)\ \{\, x := Ax \,\}$$

over $x \in \mathbb{R}^N$, where $Bx > 0$ means that every component is positive and the assignment is simultaneous. The loop *terminates* if it terminates from every initial value in $\mathbb{R}^N$. If the loop does not terminate, then $A$ has a real eigenvector $v$ for a positive real eigenvalue with $Bv \ge 0$ componentwise. Consequently, if every such eigenvector $v$ with $Bv \ge 0$ in fact has $Bv > 0$, the loop is nonterminating if and only if it is nonterminating from some eigenvector of $A$. The proof applies Brouwer's fixed-point theorem to $A$ acting on the closure of the convex, $A$-invariant set of nonterminating initial values, taken up to positive scaling.

## Informally uses

- [Brouwer's fixed-point theorem for the standard simplex](../../../../Topology/algebraic-topology/brouwer-fixed-point-theorem/exists-fixed-point.md)

## Sources

- A. Tiwari, "Termination of linear programs", *Computer Aided Verification (CAV 2004)*, LNCS 3114, Springer, 2004, pp. 70–82, author copy <https://www.csl.sri.com/users/tiwari/papers/cav04.pdf>, Section 2, Theorem 1 (one loop inequality), Theorem 2 and Corollary 2 (a conjunction of inequalities).
