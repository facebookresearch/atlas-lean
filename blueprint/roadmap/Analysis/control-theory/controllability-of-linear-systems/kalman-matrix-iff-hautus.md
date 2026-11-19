# Kalman condition and Hautus test for real matrices

Let $A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times m}$. The following are equivalent:

1. the only real row vector $\eta$ with $\eta A^k B = 0$ for all $k \in \mathbb{N}$ is $\eta = 0$;
2. for every $\lambda \in \mathbb{C}$, the only complex row vector $w$ with $w A = \lambda w$ and $w B = 0$ is $w = 0$.

Condition 1 is the Kalman rank condition $\operatorname{rank} [B, AB, \dots, A^{n-1} B] = n$ (by Cayley–Hamilton). Condition 2 says that the rows of $[\lambda I - A, B]$ are linearly independent over $\mathbb{C}$, that is, $\operatorname{rank} [\lambda I - A, B] = n$ for every $\lambda \in \mathbb{C}$. This is the equivalence (a) ⇔ (b) of Sontag, *Mathematical Control Theory* (2nd ed., 1998), Lemma 3.3.7 (the Hautus Lemma), stated here in left-eigenvector form; Sontag's (c), the same rank condition for eigenvalues $\lambda$ of $A$ only, is equivalent because $\lambda I - A$ is invertible otherwise. The proof of 2 ⇒ 1 restricts $w \mapsto w A$ to the complex subspace of row vectors annihilating every $A^k B$, which is invariant and nonzero when 1 fails, and takes an eigenvector there.

## Informally uses

- [Triangularization](../../../LinearAlgebra/eigenvalues-and-canonical-forms/triangularization/README.md): an endomorphism of a nonzero finite-dimensional complex space has an eigenvector.
