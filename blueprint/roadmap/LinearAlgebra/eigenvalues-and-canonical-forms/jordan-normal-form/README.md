# Jordan normal form

Let $A$ be a square matrix over a field $K$, indexed by a finite set, whose characteristic polynomial splits into linear factors over $K$. Then $A$ is similar to a block-diagonal matrix of Jordan blocks: $A = PJP^{-1}$ with $P$ invertible and $J$ block diagonal, each block being a Jordan block $J_s(\mu)$ of some size $s \ge 1$, the $s \times s$ matrix with $\mu$ on the diagonal, $1$ just above it and $0$ elsewhere, up to a relabelling of the indices.

## Idea

Not every matrix is diagonalizable, but over an algebraically closed field every matrix is almost diagonal. The space splits into generalized eigenspaces, one for each eigenvalue, and on each of them $A - \mu$ is nilpotent. A nilpotent map has a basis made of chains $v, Nv, N^2v, \dots$ ending in the kernel, and in the basis of a chain the map is a single Jordan block. The sizes of the blocks are determined by $A$: the number of blocks of size at least $k$ for $\mu$ is $\dim\ker(A - \mu)^k - \dim\ker(A - \mu)^{k-1}$. The Jordan form solves linear differential equations and computes matrix powers and exponentials.

## Statements

- [Jordan normal form](exists-jordan-normal-form-of-splits.md)
- [Jordan block](jordan-block.md): the Jordan block
- [Entries of a Jordan block](jordan-block-apply.md): entries of a Jordan block
- [Jordan chain basis for an endomorphism with split characteristic polynomial](exists-jordan-basis-of-charpoly-splits.md): the form for endomorphisms: a basis of Jordan chains
- [Jordan chain basis for a nilpotent endomorphism](exists-jordan-basis-of-is-nilpotent.md): the nilpotent case
- [Matrix of an endomorphism on a Jordan chain](to-matrix-eq-jordan-block.md): the matrix of an endomorphism on one chain is a Jordan block
- [Matrix of an endomorphism on a basis of Jordan chains](to-matrix-eq-block-diagonal-jordan-block.md): on several chains, a block-diagonal matrix
