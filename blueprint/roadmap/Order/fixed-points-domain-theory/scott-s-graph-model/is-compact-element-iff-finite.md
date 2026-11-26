# The compact elements of `P(ω)` are the finite sets

A set $s \subseteq \mathbb{N}$ is a compact element of the complete lattice $P(\omega)$, that is, $s \subseteq \bigcup S$ implies $s \subseteq \bigcup S_0$ for a finite $S_0 \subseteq S$, if and only if $s$ is finite. The same holds in the powerset of any set. Every set is the union of its finite subsets, so $P(\omega)$ is an algebraic lattice whose compact elements are exactly the finite sets $e_n$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, §1: each $x$ is the limit of its finite subsets). Algebraic lattices are continuous lattices, the class of domains in D. Scott, *Continuous Lattices* (Oxford PRG-7, 1971).  Algebraic lattices are also called compactly generated.

## Background

- [The `n`-th finite set of the graph model](fin-set.md): the enumeration of the compact elements.
- [Scott's characterisation theorem for `P(ω)`](mem-iff-exists-finset-of-scott-continuou.md): continuous functions are determined by their values on compact elements.

## Sources

- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, August 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>. This is the pre-publication monograph version of the paper in *Toposes, Algebraic Geometry and Logic*, Lecture Notes in Mathematics 274 (1972), 97–136; theorem numbers here are those of PRG-7.
- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
