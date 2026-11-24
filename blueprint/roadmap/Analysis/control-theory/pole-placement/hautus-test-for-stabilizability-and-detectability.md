# Hautus test for stabilizability and detectability

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$ and $C \in \mathbb{R}^{p \times n}$, and consider the continuous-time system $\dot x = A x + B u$, $y = C x$.

1. **Stabilizability.** There is $F \in \mathbb{R}^{m \times n}$ such that $A + BF$ is Hurwitz (every eigenvalue has negative real part) if and only if

    $$\operatorname{rank} \begin{bmatrix} \lambda I - A & B \end{bmatrix} = n \quad \text{for every } \lambda \in \mathbb{C} \text{ with } \operatorname{Re} \lambda \ge 0 .$$

2. **Detectability.** There is $L \in \mathbb{R}^{n \times p}$ such that $A + LC$ is Hurwitz if and only if

    $$\operatorname{rank} \begin{bmatrix} \lambda I - A \\ C \end{bmatrix} = n \quad \text{for every } \lambda \in \mathbb{C} \text{ with } \operatorname{Re} \lambda \ge 0 .$$

Writing the feedback as $u = -Kx$ instead of $u = Fx$ changes nothing ($F = -K$), and likewise $L$ may be replaced by $-L$. Part 2 is part 1 applied to the transposed pair $(A^\top, C^\top)$, since a matrix and its transpose have the same eigenvalues.

The proof in the source decomposes $(A, B)$ into its reachable and unreachable parts. The rank condition fails exactly at the roots of the characteristic polynomial $\chi_u$ of the unreachable part, and $A + BF$ can be made Hurwitz exactly when every root of $\chi_u$ has negative real part, because the reachable part can be given any characteristic polynomial by the pole-shifting theorem.

## Proof depends on

- [Hautus test for controllability](../controllability-of-linear-systems/is-controllable-on-iff-hautus.md): the rank condition at every $\lambda \in \mathbb{C}$ characterizes controllability; here it is required only on the closed right half-plane
- [Reachable and unobservable subspaces and the reduced systems](../realization-theory/reachable-and-unobservable-reductions.md): the reachable subspace is invariant and contains the range of $B$, which gives the decomposition into reachable and unreachable parts
- [Pole-shifting theorem](exists-charpoly-add-comp-eq.md): the reachable part can be assigned any characteristic polynomial
- [Exponential stability of linear differential equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): Hurwitz matrices are exactly those whose flow decays

## Background

- [Hautus test for stabilizability and detectability, discrete time](hautus-test-for-stabilizability-and-detectability-discrete-time.md): the discrete-time counterpart.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Proposition 5.5.6, equivalence of parts 3 and 4 (p. 213), with Lemma/Exercise 3.3.10 (p. 95), which identifies the roots of $\chi_u$ as the $\lambda$ with $\operatorname{rank}[\lambda I - A, B] < n$; detectability: Lemma 7.1.2 and the Hautus condition stated after it (p. 318).
