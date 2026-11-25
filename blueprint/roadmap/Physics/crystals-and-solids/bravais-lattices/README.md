# Bravais lattices

## Basis coordinates and the basis matrix

- [Basis matrix of three vectors](cartesian-matrix.md)
- [Entries of the basis matrix](cartesian-matrix-apply.md)
- [A vector is the combination of a basis with its coordinates](eq-sum-repr-smul.md)
- [Coordinates in a basis exist and are unique](eq-sum-smul-iff.md)
- [Change of basis transforms coordinates by the inverse matrix](repr-eq-inv-mul-vec-repr.md)
- [Change of basis multiplies the basis matrix by P](cartesian-matrix-eq-mul.md)
- [Change of basis multiplies the determinant by det P](det-cartesian-matrix-eq-det-mul-det.md)
- [The basis matrix is nonsingular iff the vectors are independent](det-cartesian-matrix-ne-zero-iff.md)
- [Volume of the parallelepiped spanned by three vectors](volume-parallelepiped.md)

## Orbits of finite group actions

- [The orbit sizes of a group action on a finite set add up to its size](sum-card-orbit-eq-card.md)
- [With trivial stabilizer, an orbit is as large as the finite group](card-orbit-eq-card-group-of-stabilizer-e.md)

## Bravais lattices and their lattice vectors

- [Bravais lattice given by a nonsingular basis matrix](bravais-lattice.md)
- [Primitive vectors of a Bravais lattice](primitive-vector.md)
- [The basis matrix of the primitive vectors is B](cartesian-matrix-primitive-vector.md)
- [The primitive vectors are linearly independent](linear-independent-primitive-vector.md)
- [Primitive basis of a Bravais lattice](basis.md)
- [The primitive basis consists of the primitive vectors](coe-basis.md)
- [Lattice vector of an integer cell index](lattice-vector.md)
- [The lattice vector of n is B n](lattice-vector-apply.md)
- [Lattice vectors and directions in terms of the primitive vectors](lattice-vector-eq-sum.md)
- [The primitive coordinates of a lattice vector are its index](repr-lattice-vector.md)
- [For det B ≠ 0, distinct integer vectors n give distinct vectors B n](lattice-vector-injective.md)
- [Lattice of a Bravais lattice](lattice.md)
- [The lattice consists of the vectors B n with n integral](mem-lattice-iff.md)

## Crystals with a motif

- [Crystal formed by a Bravais lattice and a finite motif](bravais-crystal.md)
- [Position of an atom of a crystal](position.md)
- [Set of atomic positions of a crystal](positions.md)
- [Translating an atom by a lattice vector shifts its cell index](lattice-vector-add-position.md)
- [Primitive coordinates of an atomic position](repr-position.md)
- [Positions determine the atoms iff offsets differ modulo the lattice](position-injective-iff.md)
- [With offsets distinct modulo the lattice, each atom has a unique index](exists-unique-index.md)

## Unimodular relabeling and cell volume

- [The primitive cell has volume the absolute determinant](volume-parallelepiped-primitive-vector.md)
- [The half-open fundamental cell has volume the absolute determinant](volume-fundamental-domain.md)
- [Relabeling a Bravais lattice by a unimodular integer matrix](relabel.md)
- [The relabeled basis matrix is B P](relabel-basis-matrix.md)
- [The change of basis to the relabeled primitive basis is P](to-matrix-basis-relabel.md)
- [Relabeling transforms primitive coordinates by P inverse](repr-basis-relabel.md)
- [A unimodular relabeling preserves the absolute determinant](abs-det-relabel.md)
- [A unimodular relabeling preserves the cell volume](volume-parallelepiped-relabel.md)
- [Relabeled lattice vectors are old lattice vectors of P n](lattice-vector-relabel.md)
- [A unimodular relabeling preserves the lattice](lattice-relabel.md)
- [Relabeling the cells of a crystal](relabel-2.md)
- [The lattice of a relabeled crystal is the relabeled lattice](relabel-to-bravais-lattice.md)
- [Relabeling the cells of a crystal moves no atom](positions-relabel.md)

## Sites of the abstract crystal

- [Abstract crystal with integer translations and the motif as unit cell](physlib-crystal.md)
- [Position of a site of the abstract crystal](site-position.md)
- [A site sits at the position of the atom with the same index and label](site-position-mk.md)
- [Translating a site by m shifts its cell index by m](vadd-mk.md)
- [Translating a site translates its position by a lattice vector](site-position-vadd.md)
- [The sites occupy exactly the atomic positions](range-site-position.md)
- [With offsets distinct modulo the lattice, sites have distinct places](site-position-injective.md)
- [Correspondence between sites and atomic positions](site-equiv-positions.md)
- [The site correspondence sends a site to its position](coe-site-equiv-positions.md)
