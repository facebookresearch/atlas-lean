# Hautus test for controllability

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$ and $T > 0$. The system $\dot x = A x + B u$ on $\mathbb{R}^n$ (with the Euclidean inner product) is controllable on $[0, T]$ if and only if for every $\lambda \in \mathbb{C}$ no nonzero complex row vector $w$ satisfies $w A = \lambda w$ and $w B = 0$; equivalently, $\operatorname{rank} [\lambda I - A, B] = n$ for every $\lambda \in \mathbb{C}$.

This is the Popov–Belevitch–Hautus test (Hautus 1969), as stated in Sontag, *Mathematical Control Theory* (2nd ed., 1998), Lemma 3.3.7, combined with the Kalman rank condition (Sontag, Theorem 3). For example, the double integrator $\ddot x = u$ passes it, and a system with $B = 0$ and $n \ge 1$ fails it.

## Informally uses

- [Kalman rank condition](is-controllable-on-iff-kalman.md): controllability is the rank condition.
- [Kalman condition and Hautus test for real matrices](kalman-matrix-iff-hautus.md): the rank condition is the eigenvector condition.
