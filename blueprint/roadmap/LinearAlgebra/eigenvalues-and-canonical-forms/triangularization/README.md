# Triangularization

Let $K$ be a field and $A$ a square matrix over $K$, indexed by a finite linearly ordered set, whose characteristic polynomial splits over $K$. Then $A = PTP^{-1}$ for some invertible matrix $P$ and some upper triangular matrix $T$ over $K$.

## Idea

Triangularization is the weak form of the Jordan normal form and is much easier to prove. The proof is an induction on the size $n$ of $A$, with nothing to prove for $n = 0$. For $n \ge 1$, if the characteristic polynomial splits, $A$ has an eigenvector $v_1$; the map induced on the quotient by the line spanned by $v_1$ again has a split characteristic polynomial, and induction produces a basis $v_1, \dots, v_n$ in which each $A v_k$ lies in the span of $v_1, \dots, v_k$. The diagonal of $T$ lists the eigenvalues with algebraic multiplicity, which gives at once $\det A = \prod \lambda_i$ and $\operatorname{tr} A = \sum \lambda_i$. Over $\mathbb{C}$ every matrix is triangularizable, even by a unitary matrix, which is Schur's theorem.

## Statements

- [Triangularization of a matrix with split characteristic polynomial](exists-upper-triangular-similar-of-split.md)
- [Triangularization of an endomorphism with split characteristic polynomial](exists-basis-upper-triangular-to-matrix.md): the form for endomorphisms

## Background

- [Characteristic polynomial](../characteristic-polynomials-and-the-cayley-hamilt/characteristic-polynomial/README.md): the polynomial that must split, whose roots are the eigenvalues
- [Existence of eigenvalues](../existence-of-eigenvalues/README.md): every operator on a nonzero finite-dimensional space over an algebraically closed field has an eigenvalue
