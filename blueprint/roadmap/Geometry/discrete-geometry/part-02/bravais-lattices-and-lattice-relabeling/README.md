# Bravais lattices and lattice relabeling

## A. Basis coordinates and the basis matrix

- [Basis matrix of three vectors](cartesian-matrix.md)
- [Entries of the basis matrix](cartesian-matrix-apply.md)
- [Coordinates of a vector of ℝ³ in a basis](eq-sum-repr-smul.md)
- [Coordinates in a basis exist and are unique](eq-sum-smul-iff.md)
- [Change of basis for coordinates](repr-eq-inv-mul-vec-repr.md)
- [Basis matrices under a change of basis](cartesian-matrix-eq-mul.md)
- [Oriented volume under a change of basis](det-cartesian-matrix-eq-det-mul-det.md)
- [Three vectors form a basis exactly when their determinant is nonzero](det-cartesian-matrix-ne-zero-iff.md)
- [Volume of a parallelepiped](volume-parallelepiped.md)
- [Orbit sizes add up to the size of a finite set](sum-card-orbit-eq-card.md)
- [Orbits with trivial stabilizer](card-orbit-eq-card-group-of-stabilizer-e.md)

## C. Bravais lattices

- [A nonsingular matrix is injective on integer vectors](mul-vec-int-cast-injective.md)
- [Bravais lattice](bravais-lattice.md)
- [Primitive vectors of a Bravais lattice](primitive-vector.md)
- [The basis matrix of the primitive vectors](cartesian-matrix-primitive-vector.md)
- [Primitive vectors are linearly independent](linear-independent-primitive-vector.md)
- [Primitive basis of a Bravais lattice](basis.md)
- [The primitive basis consists of the primitive vectors](coe-basis.md)
- [Lattice vector of a cell index](lattice-vector.md)
- [Lattice vectors are matrix products](lattice-vector-apply.md)
- [Lattice vectors as integer combinations](lattice-vector-eq-sum.md)
- [Coordinates of a lattice vector](repr-lattice-vector.md)
- [Distinct cell indices give distinct lattice vectors](lattice-vector-injective.md)
- [The lattice of a Bravais lattice](lattice.md)
- [Membership in the lattice](mem-lattice-iff.md)
- [The lattice as a set](coe-lattice.md)

## D. Crystals with a motif

- [Crystal with a motif](bravais-crystal.md)
- [Atomic position in a crystal](position.md)
- [Atomic positions of a crystal](positions.md)
- [Lattice translations move atoms between cells](lattice-vector-add-position.md)
- [Coordinates of an atomic position](repr-position.md)
- [Positions determine atoms exactly when offsets are distinct modulo the lattice](position-injective-iff.md)
- [Each atomic position has a unique cell and label](exists-unique-index.md)

## E. Unimodular relabeling and cell volume

- [Volume of the primitive cell](volume-parallelepiped-primitive-vector.md)
- [Volume of the fundamental cell](volume-fundamental-domain.md)
- [Unimodular relabeling of a Bravais lattice](relabel.md)
- [Basis matrix of a relabeled lattice](relabel-basis-matrix.md)
- [Change of basis to a relabeled lattice](to-matrix-basis-relabel.md)
- [Coordinates in a relabeled lattice](repr-basis-relabel.md)
- [Relabeling preserves the absolute determinant](abs-det-relabel.md)
- [Relabeling preserves the cell volume](volume-parallelepiped-relabel.md)
- [Lattice vectors of a relabeled lattice](lattice-vector-relabel.md)
- [Relabeling preserves the lattice](lattice-relabel.md)
- [Relabeling the cells of a crystal](relabel-2.md)
- [The lattice of a relabeled crystal](relabel-to-bravais-lattice.md)
- [Relabeling does not move atoms](positions-relabel.md)

## F. Sites of the Physlib crystal

- [Coordinate-free crystal of a motif](physlib-crystal.md)
- [Position of a crystal site](site-position.md)
- [The site of an atom sits at the atom](site-position-mk.md)
- [Translating a crystal site](vadd-mk.md)
- [Translating a site translates its position](site-position-vadd.md)
- [The sites occupy exactly the atomic positions](range-site-position.md)
- [Distinct sites occupy distinct positions](site-position-injective.md)
- [Sites correspond to atomic positions](site-equiv-positions.md)
- [The site correspondence sends a site to its position](coe-site-equiv-positions.md)
