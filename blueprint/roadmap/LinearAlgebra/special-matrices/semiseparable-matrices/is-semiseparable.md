# Semiseparable matrix

Let $K$ be a field and $N, T \in \mathbb{N}$. A lower-triangular $T \times T$ matrix $M$ over $K$
is $N$-semiseparable if every submatrix contained in its lower-triangular part, on or below the
diagonal, has rank at most $N$. Equivalently, for every $s$ with $0 \le s < T$, the block of $M$
with rows $s, \dots, T - 1$ and columns $0, \dots, s$ has rank at most $N$: a submatrix with row
set $R$ and column set $C$ lies on or below the diagonal exactly when
$\min R \ge \max C$, and it is then a submatrix of the block for $s = \max C$.

Conventions differ in the literature. This is the definition used by Dao and Gu, who restrict
semiseparability to the lower-triangular case and note that other authors would call it
$(N, 0)$-semiseparability or a form of quasiseparability.

Low semiseparable rank is not low matrix rank: the lower-triangular $T \times T$ matrix whose
entries on and below the diagonal all equal $1$ (the matrix of cumulative sums) is
$1$-semiseparable, since every such block has all its entries equal to $1$, and it is invertible,
of rank $T$.

## Sources

- T. Dao and A. Gu, "Transformers are SSMs: Generalized Models and Efficient Algorithms Through Structured State Space Duality", arXiv:2405.21060 (version 1), Section 3.2, Definition 3.1 and Remark 2.
