# Reachable and unobservable subspaces and the reduced systems

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, $X = \mathbb{K}^n$ with $n \ge 0$, and let $A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$, $C \in \mathbb{K}^{p \times n}$. Its **Markov parameters** are the matrices $C A^{i-1} B$, $i \ge 1$. Let

$$\mathcal{R} = \operatorname{range} R(A, B), \qquad \mathcal{N} = \ker O(A, C),$$

the reachable and unobservable subspaces, with $R$ and $O$ the reachability and observability matrices (for $n = 0$ these are empty matrices and $\mathcal{R} = \mathcal{N} = X = \{0\}$). Then:

1. $\mathcal{R}$ is invariant under $A$ and contains the column space of $B$. The **reachable restriction** $(A|_{\mathcal{R}},\ B,\ C|_{\mathcal{R}})$, with $B$ viewed as a map into $\mathcal{R}$, is controllable and has the same Markov parameters as $(A, B, C)$.
2. $\mathcal{N}$ is invariant under $A$ and contained in $\ker C$. On the quotient $X / \mathcal{N}$, with $\pi : X \to X/\mathcal{N}$ the projection, the induced triple $(\bar A, \pi B, \bar C)$, defined by $\bar A \pi = \pi A$ and $\bar C \pi = C$, is observable and has the same Markov parameters as $(A, B, C)$.
3. Applying the quotient construction of part 2 to the reachable restriction of part 1 gives a triple that is controllable and observable and has the same Markov parameters as $(A, B, C)$; it is similar to the canonical triple $(A_{11}, B_{11}, C_{11})$ of Sontag's Lemma 6.5.1.

In coordinates adapted to these subspaces the reductions are Sontag's block decompositions: $T^{-1} A T = \begin{bmatrix} A_1 & A_2 \\ 0 & A_3 \end{bmatrix}$, $T^{-1} B = \begin{bmatrix} B_1 \\ 0 \end{bmatrix}$ for the controllability decomposition, with $(A_1, B_1)$ controllable and $C A^{i-1} B = C_1 A_1^{i-1} B_1$ for $C T = (C_1\ C_2)$; the dual observability decomposition with $C T = (C_1\ 0)$ and $(A_1, C_1)$ observable; and their combination (Lemma 6.5.1), whose $(A_{11}, B_{11}, C_{11})$ is canonical with the same Markov parameters (Lemma/Exercise 6.5.2). The invariance of $\mathcal{R}$ and $\mathcal{N}$ is the Cayley–Hamilton theorem; the equality of Markov parameters follows from $A^{i-1} B$ having its columns in $\mathcal{R}$ and from $C$ vanishing on $\mathcal{N}$.

## Depends on

- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): the reachability matrix $R(A, B)$ and controllability.
- [Observability of discrete-time linear systems over a finite horizon](../observability-of-linear-systems/observability-rank-condition-discrete-time.md): the observability matrix $O(A, C)$ and observability.

## Proof depends on

- [Cayley–Hamilton theorem](../../../LinearAlgebra/eigenvalues-and-canonical-forms/characteristic-polynomials-and-the-cayley-hamilt/cayley-hamilton-theorem/aeval-self-charpoly.md): $A$-invariance of $\mathcal{R}$ and $\mathcal{N}$.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Lemma 3.3.3 with its proof and Lemma/Exercise 3.3.4 (p. 93); the observability decomposition (6.8) (p. 272); Lemma 6.5.1, Lemma/Exercise 6.5.2 and Definition 6.5.3 (pp. 283–284).
