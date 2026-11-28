# Coulomb matrix representation of a molecule

The Coulomb matrix encodes nuclear charges and geometry in one symmetric matrix: off-diagonal entries are the nuclear repulsion of a pair, diagonal entries an empirical fit of free-atom energy to charge. It is the input of a regression from geometry to molecular energy.

For nuclei $I = 1, \dots, n$ of charges $Z_I > 0$ at pairwise distinct positions $\mathbf{R}_I \in \mathbb{R}^3$, the Coulomb matrix $\mathbf{M} \in \mathbb{R}^{n \times n}$ is

$$
M_{IJ} = \begin{cases} 0.5\, Z_I^{2.4}, & I = J \\[2pt] \dfrac{Z_I Z_J}{|\mathbf{R}_I - \mathbf{R}_J|}, & I \neq J . \end{cases}
$$

The matrix is symmetric, and the off-diagonal entries are finite because the positions are pairwise distinct. In atomic units the off-diagonal entry is the nuclear repulsion energy of the pair; the diagonal entry is an empirical fit, not a Coulomb integral, with the factor $0.5$ and the exponent $2.4$ of the source.

Its invariances are immediate. Relabelling the nuclei by a permutation $P$ replaces $\mathbf{M}$ by $P\mathbf{M}P^{\top}$. Applying any Euclidean isometry of $\mathbb{R}^{3}$, a reflection included, leaves $\mathbf{M}$ unchanged, since only interatomic distances enter; two enantiomers therefore share a Coulomb matrix, and nothing about bonding or stereochemistry is recorded. The entries also determine the data they are built from: the diagonal determines each $Z_I$, because $z \mapsto 0.5 z^{2.4}$ is strictly increasing on the positive reals, and the off-diagonal entries then determine every interatomic distance.

That a labelled point configuration is itself determined, up to Euclidean isometries including reflections, by its matrix of pairwise distances is a standard fact of distance geometry. It is context here, not a result of this page: proving it needs the centred Gram reconstruction and an extension-of-isometry argument.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes a finite index type for the nuclei, charges in $\mathbb{R}_{>0}$ and positions in a Euclidean space with the injectivity hypothesis, defines $\mathbf{M}$ by the display, and proves symmetry, invariance under isometries, the conjugation law under relabelling, and the recovery of charges and distances from the entries, the first of these from strict monotonicity of the real power $z \mapsto z^{2.4}$. Reconstruction of the configuration from its distance matrix is a separate statement and would be a prerequisite of any page that asserts it.

## Context

Graduate. The first general-purpose descriptor used to learn molecular energies, by Rupp, Tkatchenko, Müller and von Lilienfeld; this chapter treats it as a representation with its invariances, not as an electronic-structure model.

## Sources

- Matthias Rupp, Alexandre Tkatchenko, Klaus-Robert Müller and O. Anatole von Lilienfeld, *Fast and Accurate Modeling of Molecular Atomization Energies with Machine Learning*, Physical Review Letters 108 (2012) 058301, Eq. 1 and the paragraph that follows it. DOI [10.1103/PhysRevLett.108.058301](https://doi.org/10.1103/PhysRevLett.108.058301), arXiv:[1109.2618v1](https://arxiv.org/abs/1109.2618v1).
