# Kneser $p$-neighbors

Let $R$ be a commutative ring, $M$ an $R$-module and $p$ a natural number. Two submodules $L_1$ and $L_2$ of $M$ are $p$-neighbors when $p$ is prime and $L_1 \cap L_2$ has index $p$ in each of them: the quotients $L_1/(L_1 \cap L_2)$ and $L_2/(L_1 \cap L_2)$ both have exactly $p$ elements.

## Idea

Kneser's neighbor method explores the lattices in a genus by small steps. Starting from one integral lattice, one passes to a neighbor that agrees with it on a sublattice of index $p$ and differs only there; repeated steps are used to enumerate the isometry classes of a genus. The relation is symmetric, and the prime condition rules out trivial cases such as $p = 1$, where the two submodules would simply coincide with their intersection. In $\mathbb{Q}^2$, the lattices $\mathbb{Z} \times \mathbb{Z}$ and $p\mathbb{Z} \times \tfrac1p\mathbb{Z}$ meet in $p\mathbb{Z} \times \mathbb{Z}$, which has index $p$ in each, so they are $p$-neighbors.

## Statements

- [$p$-neighbors of submodules](are-pneighbors.md)
- [The $p$-neighbor relation is symmetric](are-pneighbors-comm.md): the relation is symmetric
- [No submodules are $1$-neighbors](not-are-pneighbors-one.md): the prime condition excludes $p = 1$
