# Convergence of normalized powers of a primitive matrix

Let $A$ be a nonnegative primitive $n \times n$ matrix ($A^m$ has all entries positive for some $m \ge 1$), with Perron root $r > 0$ and positive right eigenvector $u$. Then $A$ has a positive left eigenvector $v$ for $r$, normalized by $v^{\mathsf T}u = 1$, and $(A/r)^k \to uv^{\mathsf T}$ as $k \to \infty$. Proof: with $D = \operatorname{diag}(u)$, the matrix $S = D^{-1}(A/r)D$ is row-stochastic and primitive; if $\pi$ is its stationary distribution then $S^k \to \mathbf 1\pi^{\mathsf T}$, and $(A/r)^k = DS^kD^{-1} \to u(\pi^{\mathsf T}D^{-1})$, where $v^{\mathsf T} = \pi^{\mathsf T}D^{-1}$ is a positive left eigenvector with $v^{\mathsf T}u = \pi^{\mathsf T}\mathbf 1 = 1$. Primitivity cannot be weakened to irreducibility: for the $2 \times 2$ permutation matrix swapping the coordinates, $r = 1$ and the powers alternate.

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](perron-frobenius.md): positive Perron eigenvector of an irreducible matrix.
- [The convergence theorem](../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-tv-dist-pow-le.md): convergence of powers of a primitive stochastic matrix to its stationary distribution.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- A finite irreducible stochastic matrix has a stationary distribution with all entries positive.
- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
