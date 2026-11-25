# Scott's extension theorem

Let $X$ be a subspace of a topological space $Y$. Every continuous map $f : X \to P(\omega)$, for the Scott topology, extends to a continuous map $Y \to P(\omega)$, so $P(\omega)$ is an injective space (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), Theorem 1.5). The extension is [Scott's extension](extend-scott.md) $\bar f$, which is [continuous](continuous-extend-scott.md) and [agrees with $f$ on $X$](extend-scott-apply.md); those pages state the theorem for this map.

With the embedding theorem, every countably based $T_0$ space sits in $P(\omega)$ and every continuous map into $P(\omega)$ extends: this is why Scott can work inside the single space $P(\omega)$. Scott's *Continuous Lattices* (Oxford PRG-7, 1971, Theorem 2.12) shows more generally that the injective $T_0$ spaces are exactly the continuous lattices with their Scott topologies.

## Informally uses

- [Scott's extension is continuous](continuous-extend-scott.md): continuity of the extension.
- [Scott's extension extends a continuous map](extend-scott-apply.md): the extension property.

## Background

- [Scott's embedding theorem](exists-is-embedding-with-scott.md): the companion theorem.
- [Continuous lattice](../continuous-lattices/is-continuous-lattice.md): the general class of injective spaces.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, August 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>. This is the pre-publication monograph version of the paper in *Toposes, Algebraic Geometry and Logic*, Lecture Notes in Mathematics 274 (1972), 97–136; theorem numbers here are those of PRG-7.
