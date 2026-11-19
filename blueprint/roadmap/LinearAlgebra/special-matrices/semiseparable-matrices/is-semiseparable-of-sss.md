# Sequentially semiseparable matrices are semiseparable

Let $N, T \in \mathbb{N}$, let $B_0, \dots, B_{T-1}, C_0, \dots, C_{T-1} \in \mathbb{R}^N$ and
$A_0, \dots, A_{T-1} \in \mathbb{R}^{N \times N}$, and let $M$ be the lower-triangular
$T \times T$ matrix with entries $M_{ji} = C_j^{\mathsf{T}} A_j A_{j-1} \cdots A_{i+1} B_i$ for
$j \ge i$ (the product of the $A$'s is the identity when $j = i$) and $M_{ji} = 0$ for $j < i$. Then $M$ is [$N$-semiseparable](is-semiseparable.md).

Proof: fix $s$ and take the block of rows $j \ge s$ and columns $i \le s$. Each of its entries
factors as $M_{ji} = \big(C_j^{\mathsf{T}} A_j \cdots A_{s+1}\big)\big(A_s \cdots A_{i+1} B_i\big)$,
a row vector of length $N$ times a column vector of length $N$. So the block is the product of a
matrix with $N$ columns and a matrix with $N$ rows, and its rank is at most $N$.

The paper's printed proof factors the blocks strictly below the diagonal; blocks that meet the
diagonal use the same split with an empty product. If a model adds a feed-through term, the matrix
becomes $M + \operatorname{diag}(D_0, \dots, D_{T-1})$: its blocks strictly below the diagonal
still have rank at most $N$, but a block that meets the diagonal contains at most one diagonal
entry, so the bound for blocks on or below the diagonal becomes $N + 1$.

Dao and Gu call this the $N$-sequentially semiseparable (SSS) representation. The converse, that
every $N$-semiseparable matrix has such a representation, is their Proposition 3.4 and is not
covered here.

## Informally uses

- [Rank of a product of matrices](../../linear-maps-and-duality/rank-of-a-product.md):
  mathematical prerequisite, the rank bound for each block.

## Sources

- T. Dao and A. Gu, "Transformers are SSMs: Generalized Models and Efficient Algorithms Through Structured State Space Duality", arXiv:2405.21060 (version 1), Section 3.2.1, Definition 3.2, equation (4), Lemma 3.3 and its proof, equation (5), and Proposition 3.4.
