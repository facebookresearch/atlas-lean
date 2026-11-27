# Partial trace

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $m$ and $n$ be finite index sets. The partial trace over the first factor maps a square matrix $A$ with rows and columns indexed by $m \times n$ to the $n \times n$ matrix

$$\operatorname{tr}_1(A)_{j j'} = \sum_{i \in m} A_{(i, j), (i, j')};$$

the partial trace over the second factor sums over the second index instead and gives an $m \times m$ matrix.

## Idea

A matrix indexed by $m \times n$ acts on the tensor product $\mathbb{K}^m \otimes \mathbb{K}^n$, and the partial trace traces out one factor. It is the unique linear map with $\operatorname{tr}_1(X \otimes Y) = \operatorname{tr}(X)\, Y$. In quantum mechanics, if $\rho$ is the density matrix of a system made of two parts, $\operatorname{tr}_1(\rho)$ is the state of the second part alone: the partial trace preserves positive semidefiniteness and the trace, so it sends density matrices to density matrices. It is adjoint, for the trace pairing, to the map $Y \mapsto I \otimes Y$. Applied to a pure state $uu^*$, it gives the reduced density matrix whose eigenvalues measure the entanglement of $u$.

## Statements

- [Partial trace over the first factor](partial-trace-left.md)
- [Partial trace over the second factor](partial-trace-right.md): the partial trace over the second factor
- [Left partial trace of a rank-one matrix](partial-trace-left-vec-mul-vec-star.md): partial trace of a rank-one matrix $uu^*$
- [Right partial trace of a rank-one matrix](partial-trace-right-vec-mul-vec-star.md): the same, over the second factor
- [Left partial trace preserves positive semidefiniteness](pos-semidef-partial-trace-left.md): it preserves positive semidefiniteness
- [Right partial trace preserves positive semidefiniteness](pos-semidef-partial-trace-right.md): the same, over the second factor
- [Left partial trace is adjoint to identity amplification](trace-partial-trace-left-mul.md): adjointness to $Y \mapsto I \otimes Y$
- [Right partial trace is adjoint to identity amplification](trace-partial-trace-right-mul.md): the same, over the second factor
- [Left partial trace of a density matrix has trace one](trace-partial-trace-left-of-trace-eq-one.md): it preserves the trace, so density matrices go to density matrices
- [Right partial trace of a density matrix has trace one](trace-partial-trace-right-of-trace-eq-on.md): the same, over the second factor
- [Characterization of the partial trace by the product rule](remaining-clauses-of-partial-trace-and-reduced-states.md): the unique linear map with $\operatorname{tr}_1(X \otimes Y) = \operatorname{tr}(X)\, Y$
