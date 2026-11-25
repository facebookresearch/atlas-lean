# Diagonalization

Let $K$ be a field and $A$ a square matrix over $K$ indexed by a finite set. If the characteristic polynomial of $A$ splits over $K$ and its minimal polynomial is squarefree, then $A = PDP^{-1}$ for some invertible matrix $P$ and some diagonal matrix $D$ over $K$.

## Idea

A matrix is diagonalizable when its space has a basis of eigenvectors. The minimal polynomial detects this: if it is a product of distinct linear factors $(x - \lambda_1)\cdots(x - \lambda_k)$, the kernels of $A - \lambda_i$ together span the whole space, by the kernels lemma. Squarefreeness alone makes the linear map semisimple, and the split characteristic polynomial supplies the eigenvalues in $K$. For example, a projection, with $A^2 = A$, has minimal polynomial dividing $x(x - 1)$ and is always diagonalizable, while the Jordan block $\begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$, with minimal polynomial $x^2$, is not.

## Statements

- [Diagonalizability from a split characteristic polynomial and a squarefree minimal polynomial](exists-diagonal-similar-of-splits-of-squ.md)
- [Eigenbasis of a semisimple endomorphism with split characteristic polynomial](exists-eigenbasis-of-is-semisimple-of-sp.md): the form for endomorphisms: a semisimple endomorphism with split characteristic polynomial has an eigenbasis
