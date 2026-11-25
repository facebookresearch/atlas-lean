# Semicircle moments count Dyck words

For every $k \in \mathbb{N}$, the $2k$-th moment of the semicircle distribution $\sigma$ is the
number of Dyck words of semilength $k$, the words of $k$ up-steps and $k$ down-steps none of whose
prefixes has more down-steps than up-steps:

$$\int x^{2k} \, d\sigma(x) = \#\{\text{Dyck words of semilength } k\}.$$

These words encode the non-crossing pairings that survive in the moment method.

## Informally uses

- [Dyck paths and lattice walks](../../../Combinatorics/catalan-numbers-lattice-paths/dyck-paths-lattice-walks/README.md):
  the count of Dyck words of semilength $k$ by the Catalan number $C_k$.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Lemma 2.3.15, and §2.4.2, Exercise 2.4.9.
