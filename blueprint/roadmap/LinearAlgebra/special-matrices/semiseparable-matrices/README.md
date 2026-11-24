# Semiseparable matrices

Let $K$ be a field and $N, T \in \mathbb{N}$. A lower-triangular $T \times T$ matrix $M$ over $K$ is $N$-semiseparable if every submatrix contained in its lower-triangular part, on or below the diagonal, has rank at most $N$; equivalently, for every $s < T$ the block with rows $s, \dots, T - 1$ and columns $0, \dots, s$ has rank at most $N$.

## Idea

Semiseparable matrices are structured matrices whose blocks below the diagonal have low rank, although the matrix itself may have full rank: the lower-triangular matrix of ones, which computes cumulative sums, is $1$-semiseparable and invertible. A matrix built from products $C_j^{\mathsf T} A_j \cdots A_{i+1} B_i$ of small matrices, the sequentially semiseparable form, is semiseparable of rank at most the state dimension. Such matrices can be applied to a vector in time linear in $T$. In machine learning, they are the matrices by which linear state-space sequence models act along a sequence, which relates those models to attention.

## Statements

- [Semiseparable matrix](is-semiseparable.md)
- [Sequentially semiseparable matrices are semiseparable](is-semiseparable-of-sss.md): sequentially semiseparable matrices are semiseparable

## Related topics

- [Linear state-space sequence models](../../../ComputerScience/machine-learning/linear-state-space-sequence-models/README.md): the matrices by which these models act along the sequence.
