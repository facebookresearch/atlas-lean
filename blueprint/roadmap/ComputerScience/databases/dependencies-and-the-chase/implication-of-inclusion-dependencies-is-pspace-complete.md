# Implication of inclusion dependencies is PSPACE-complete

An inclusion dependency over a schema has the form $R[i_1, \dots, i_k] \subseteq P[j_1, \dots, j_k]$ and holds in a
database when the projection of $R$ on positions $i_1, \dots, i_k$ is contained in the projection of $P$ on positions
$j_1, \dots, j_k$. The problem of deciding, for a set $\Sigma$ of inclusion dependencies and an inclusion dependency
$\sigma$, whether every finite database satisfying $\Sigma$ satisfies $\sigma$ is PSPACE-complete.

## Depends on

- [Inclusion dependencies and finite implication](inclusion-dependencies-and-finite-implication.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Finite and unrestricted implication of functional and inclusion dependencies](finite-and-unrestricted-implication-of-functional-and-inclusion.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 11.9 (p. 82), Lemma 11.10 (p. 82), Theorem 11.11 and Corollary 11.12 (p. 83), and Exercise 1.17 (p. 88).
