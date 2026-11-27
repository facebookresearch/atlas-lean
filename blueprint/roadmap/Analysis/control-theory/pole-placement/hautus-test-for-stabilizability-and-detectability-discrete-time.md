# Hautus test for stabilizability and detectability, discrete time

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$ and $C \in \mathbb{R}^{p \times n}$, and consider the discrete-time system $x(k+1) = A x(k) + B u(k)$, $y(k) = C x(k)$.

1. **Stabilizability.** There is $F \in \mathbb{R}^{m \times n}$ such that $A + BF$ is convergent (every eigenvalue has modulus less than $1$; a Schur matrix) if and only if

    $$\operatorname{rank} \begin{bmatrix} \lambda I - A & B \end{bmatrix} = n \quad \text{for every } \lambda \in \mathbb{C} \text{ with } |\lambda| \ge 1 .$$

2. **Detectability.** There is $L \in \mathbb{R}^{n \times p}$ such that $A + LC$ is convergent if and only if

    $$\operatorname{rank} \begin{bmatrix} \lambda I - A \\ C \end{bmatrix} = n \quad \text{for every } \lambda \in \mathbb{C} \text{ with } |\lambda| \ge 1 .$$

Writing the feedback as $u = -Kx$ changes nothing ($F = -K$), and $L$ may be replaced by $-L$. Part 2 is part 1 for $(A^\top, C^\top)$.

The proof is the continuous-time one with the unit disc in place of the left half-plane. The rank condition fails exactly at the roots of the characteristic polynomial of the unreachable part. The reachable part can be given any characteristic polynomial, in particular one whose roots lie in the open unit disc.

## Proof depends on

- [Hautus test for controllability](../controllability-of-linear-systems/is-controllable-on-iff-hautus.md): the rank condition at every $\lambda \in \mathbb{C}$ characterizes controllability; here it is required only outside the open unit disc
- [Reachable and unobservable subspaces and the reduced systems](../realization-theory/reachable-and-unobservable-reductions.md): the reachable subspace is invariant and contains the range of $B$, which gives the decomposition into reachable and unreachable parts
- [Pole-shifting theorem](exists-charpoly-add-comp-eq.md): the reachable part can be assigned any characteristic polynomial
- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): convergent matrices are exactly those whose powers decay

## Background

- [Hautus test for stabilizability and detectability](hautus-test-for-stabilizability-and-detectability.md): the continuous-time version

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Proposition 5.5.6, discrete-time case of the equivalence of parts 3 and 4 (p. 213), with Lemma/Exercise 3.3.10 (p. 95); detectability: Lemma 7.1.2 and the discrete-time Hautus condition stated after it (p. 318).
