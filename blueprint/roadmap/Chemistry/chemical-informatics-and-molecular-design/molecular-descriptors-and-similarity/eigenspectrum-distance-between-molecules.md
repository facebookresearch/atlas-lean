# Eigenspectrum distance between molecules

Molecules are compared by the Euclidean distance between the sorted eigenvalue spectra of their Coulomb matrices, the shorter spectrum padded with zeros. Sorting by decreasing absolute value needs a tie rule, and with one fixed the distance is unchanged by relabelling atoms or moving a molecule rigidly.

Let $\mathbf{M}$ and $\mathbf{M}'$ be the Coulomb matrices of two molecules with $n$ and $n'$ nuclei. Both are real symmetric, so their eigenvalues are real; list each with multiplicity, sorted by decreasing absolute value and, among equal absolute values, by decreasing signed value, and extend the shorter list by zeros to length $\max(n, n')$. Writing $\epsilon$ and $\epsilon'$ for the two lists,

$$
d(\mathbf{M}, \mathbf{M}') = \sqrt{\sum_{I} |\epsilon_I - \epsilon'_I|^2} .
$$

The source prescribes the decreasing-magnitude order and the zero padding; the tie rule is a convention added here, because without it the order of two eigenvalues of equal magnitude and opposite sign is undecided and the value of $d$ is not determined. With it, $d$ is a well-defined pseudometric, invariant under relabelling of the nuclei, since $P\mathbf{M}P^{\top}$ has the same eigenvalue multiset, and under Euclidean isometries of either molecule, since $\mathbf{M}$ itself is. Distinct molecules with the same spectrum lie at distance zero.

Continuity holds wherever the eigenvalue magnitudes are strictly separated, and fails in general at crossings of eigenvalues of opposite sign. Repeated eigenvalues are not by themselves a problem: for a configuration whose Coulomb matrix is positive definite, magnitude sorting is ordinary signed sorting, which stays continuous through a repeated positive eigenvalue, as happens for a weakly coupled equilateral three-nucleus configuration. The crossing that breaks continuity is the opposite-sign one: three equal charges with common diagonal $a > 0$ and off-diagonal entries $3a/2, a/\sqrt{2}, a/\sqrt{2}$ have eigenvalues $3a, a/2, -a/2$, and varying the two equal entries through $a/\sqrt{2}$ swaps the last two coordinates of the magnitude-sorted list.

## Depends on

- [Coulomb matrix representation of a molecule](coulomb-matrix-representation.md)
- [Eigenvalues of a linear map](../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/eigenvalues.md)

## Proof depends on

- [Hoffman–Wielandt inequality for Hermitian matrices](../../../LinearAlgebra/positive-definite-matrices/hoffman-wielandt-inequality/hoffman-wielandt-hermitian.md)

## Expansion

A formal development defines the eigenvalue list of a real symmetric matrix with multiplicity, the magnitude-then-sign ordering and the zero padding, then defines $d$ as a Euclidean norm, from which nonnegativity, symmetry and the triangle inequality follow. Permutation invariance comes from preservation of the eigenvalue multiset under conjugation, for instance through the characteristic polynomial; isometry invariance is invariance of the matrix itself. Continuity on the strict-gap set is the signed-order continuity the linked Hoffman–Wielandt inequality gives, composed with the reordering, which is locally constant there.

## Context

Graduate. The similarity measure Rupp, Tkatchenko, Müller and von Lilienfeld pair with the Coulomb matrix, so that the symmetries of a molecule are symmetries of its representation.

## Sources

- Matthias Rupp, Alexandre Tkatchenko, Klaus-Robert Müller and O. Anatole von Lilienfeld, *Fast and Accurate Modeling of Molecular Atomization Energies with Machine Learning*, Physical Review Letters 108 (2012) 058301, the paragraph after Eq. 1, which gives the distance, the decreasing-absolute-value ordering, the zero padding and criteria (i)–(iv). DOI [10.1103/PhysRevLett.108.058301](https://doi.org/10.1103/PhysRevLett.108.058301), arXiv:[1109.2618v1](https://arxiv.org/abs/1109.2618v1).
