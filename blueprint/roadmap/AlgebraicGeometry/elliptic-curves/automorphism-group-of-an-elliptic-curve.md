# Automorphism groups of elliptic curves

Over an algebraically closed field an elliptic curve has exactly two automorphisms, $\pm1$, unless its $j$-invariant is $0$ or $1728$, where it has $4$, $6$, $12$ or $24$ depending on the characteristic.

Let $E$ be an elliptic curve over an algebraically closed field $k$, and let $\operatorname{Aut}(E)$ be the group of isomorphisms $E\to E$ that fix the origin, under composition; it contains $[-1]$. Then $\#\operatorname{Aut}(E)$ divides $24$, and

- $\#\operatorname{Aut}(E)=2$, that is $\operatorname{Aut}(E)=\{\pm1\}$, if $j(E)\ne 0,1728$;
- $\#\operatorname{Aut}(E)=4$ if $j(E)=1728$ and $\operatorname{char}k\ne 2,3$;
- $\#\operatorname{Aut}(E)=6$ if $j(E)=0$ and $\operatorname{char}k\ne 2,3$;
- $\#\operatorname{Aut}(E)=12$ if $j(E)=0$ and $\operatorname{char}k=3$;
- $\#\operatorname{Aut}(E)=24$ if $j(E)=0$ and $\operatorname{char}k=2$.

In characteristic $2$ and $3$ the values $0$ and $1728$ of the $j$-invariant coincide. For a prime $p$ and $j$ in the field with $p$ elements, the five cases say $\#\operatorname{Aut}(E)=2\cdot\operatorname{autWeight}(p,j)$, with the [automorphism weight](../../NumberTheory/not-yet-classified/supersingular-jset/aut-weight.md) of the supersingular $j$-invariant pages. When $\operatorname{char}k\ne 2,3$, the curve $y^2=x^3+x$ has $j=1728$ and the extra automorphism $(x,y)\mapsto(-x,iy)$ with $i^2=-1$, and $y^2=x^3+1$ has $j=0$ and the extra automorphism $(x,y)\mapsto(\zeta x,y)$ with $\zeta^3=1\ne\zeta$.

## Depends on

- [Aut Weight](../../NumberTheory/not-yet-classified/supersingular-jset/aut-weight.md)

## Proof depends on

- [Variable changes give additive equivalences of points](weierstrass-curves/variable-change-add-equiv.md)

## Expansion

An automorphism fixing the origin is a change of Weierstrass variables $(x,y)\mapsto(u^2x+r,u^3y+su^2x+t)$ preserving the equation. For $\operatorname{char}k\ne 2,3$ and the short form $y^2=x^3+Ax+B$ these are $(x,y)\mapsto(u^2x,u^3y)$ with $u^4A=A$ and $u^6B=B$: if $AB\ne0$ (that is $j\ne 0,1728$) then $u^2=1$; if $B=0$ then $u^4=1$; if $A=0$ then $u^6=1$. In characteristic $2$ and $3$ the curve with $j=0$ needs the general change of variables, and one finds groups of order $24$ and $12$ (Galbraith, Exercise 9.4.5, does characteristic $2$). A good expansion adds a page for the action of Weierstrass variable changes on the coefficients and the $j$-invariant, building on the existing variable-change pages.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Definition 9.4.1, Example 9.4.2, Theorem 9.4.4 (citing Silverman, Theorem III.10.1 and Proposition A.1.2) and Exercise 9.4.5.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2022, [Lecture 22: Isogeny volcanoes](https://math.mit.edu/classes/18.783/2022/LectureNotes22.pdf), Remark 22.2.
