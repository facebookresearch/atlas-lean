# Cayley–Hamilton theorem

Let $R$ be a commutative ring, $M$ a free and finitely generated $R$-module, and $f \colon M \to M$ an $R$-linear map.
Let $\chi_f = \det(X \cdot 1 - A) \in R[X]$ be the characteristic polynomial of $f$, where $A$ is the matrix of $f$ in
a basis of $M$. Then $\chi_f(f) = 0$: replacing $X$ by $f$, with $X^k$ read as the $k$-th power of $f$ under
composition and a constant $c$ as $c$ times the identity, gives the zero map. This is the general form of the theorem
that every linear operator $T$ on a nonzero finite-dimensional vector space $V$ over a field $F$ is a zero of its
characteristic polynomial: take $R = F$, $M = V$, which is free and finitely generated, and $f = T$.

## Idea

Every $n \times n$ matrix with entries in a nonzero commutative ring satisfies a monic polynomial equation of degree
$n$, with coefficients computed from its entries; for $n = 2$ it reads
$A^2 - (\operatorname{tr} A)\, A + (\det A)\, 1 = 0$. So $A^n$ is a linear combination of $1, A, \dots, A^{n-1}$, and
over a field the minimal polynomial of $A$ divides $\chi_A$. A classical proof uses the adjugate:
$(X \cdot 1 - A)\operatorname{adj}(X \cdot 1 - A) = \chi_A(X) \cdot 1$ for matrices with entries in $R[X]$; writing the
adjugate as $\sum_k B_k X^k$, comparing the coefficients of $X^k$ on both sides and multiplying that equation by $A^k$
on the left, the sum over $k$ telescopes to $\chi_A(A) = 0$. The polynomial does not depend on the basis. Some books
define the characteristic polynomial as $\det(A - X \cdot 1) = (-1)^n \chi_A$; the theorem holds for either sign.

## Statements

- [Cayley–Hamilton theorem for endomorphisms of finite free modules](aeval-self-charpoly.md)

## Background

- [Characteristic polynomial](../characteristic-polynomial/README.md): the characteristic polynomial of an operator

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 9.64, the case of operators on nonzero finite-dimensional real or complex vector spaces (version read: the open-access PDF dated 4 November 2026).
