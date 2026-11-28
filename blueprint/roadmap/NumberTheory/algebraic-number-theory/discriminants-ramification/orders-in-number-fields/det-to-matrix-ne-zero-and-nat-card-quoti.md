# The index of a subgroup of full rank as a determinant

Let $M$ be a free abelian group
with a basis $(\alpha_i)_{i \in \iota}$, $\iota$ finite, and let $N \subseteq M$ be a subgroup
with a basis $(\beta_j)_{j \in \iota}$ indexed by the same set (so $N$ is free of the same rank).
Let $T$ be the matrix with $\beta_j = \sum_i T_{ij} \alpha_i$ (`b.toMatrix`). Then
$\det T \neq 0$, the quotient $M/N$ is finite, and $(M : N) = \#(M/N) = |\det T|$.

This is F. Keune, *Number Fields*, 2023, Lemma 1.40 (p. 20), for bases indexed by
$\{1, \dots, n\}$; here they are indexed by any finite type. Keune's transition matrix is $T$ or
its transpose, which has the same determinant. The equality alone is Mathlib's
`Submodule.natAbs_det_basis_change` (and `AddSubgroup.index_eq_natAbs_det`); neither asserts
$\det T \neq 0$ or the finiteness of $M/N$ (`Nat.card` of an infinite type is $0$).
