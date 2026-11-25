# Trace and determinant are similarity invariants

Let $R$ be a commutative ring, $M$ and $N$ two $R$-modules, $e : M \to N$ a linear isomorphism, and $f$ and $g$ endomorphisms of $M$ and $N$ with $e \circ f = g \circ e$. Then $\operatorname{tr} f = \operatorname{tr} g$ and $\det f = \det g$. (For a module without a finite basis, the trace is taken to be $0$ and the determinant $1$.)

## Idea

Two endomorphisms related by an isomorphism, $g = efe^{-1}$, are the same map written in different coordinates, so any quantity computed from a matrix that does not depend on the basis must agree for them. Trace and determinant are the first such invariants, and for a finitely generated free module of rank two over a nontrivial ring they determine the characteristic polynomial: $\chi_f(X) = X^2 - (\operatorname{tr} f)X + \det f$. Similarity invariants are how one tells matrices apart: two matrices with different traces cannot be similar.

## Statements

- [Trace and determinant are invariant under semiconjugacy](trace-eq-and-det-eq-of-semiconj.md)
- [Characteristic polynomial of an endomorphism of a free module of rank two](charpoly-of-finrank-eq-two.md): in rank two the characteristic polynomial is $X^2 - (\operatorname{tr} f)X + \det f$, so with the main statement two such endomorphisms related by an isomorphism have the same characteristic polynomial
