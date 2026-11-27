# Composition, sum and double-dual rules for dual isogenies

Taking duals reverses composition, is additive, is an involution, and fixes the multiplication maps.

Let $E$, $E'$, $E''$ be elliptic curves over a field $k$, and use the convention that the dual of the zero isogeny is zero. For isogenies $\varphi,\psi\colon E\to E'$ and $\chi\colon E'\to E''$, with [duals](dual-isogeny.md) $\hat\varphi$, $\hat\psi$, $\hat\chi$:

1. $\widehat{\chi\circ\varphi}=\hat\varphi\circ\hat\chi$;
2. $\widehat{\varphi+\psi}=\hat\varphi+\hat\psi$, where $\varphi+\psi$ is the pointwise sum, again an isogeny;
3. $\hat{\hat\varphi}=\varphi$;
4. $\widehat{[m]}=[m]$ for every integer $m$.

## Depends on

- [Existence and uniqueness of the dual isogeny](dual-isogeny.md)

## Proof depends on

- [Degrees of isogenies multiply under composition](degree-is-multiplicative.md)
- [Multiplication by m has degree m squared](degree-of-multiplication-by-m.md)

## Expansion

If $\varphi$ or $\chi$ is zero, items 1 and 3 hold by the convention $\hat0=0$, and item 4 for $m=0$ is $\hat0=0$; so assume the maps are nonzero, where uniqueness of the dual applies. Item 1: $(\hat\varphi\circ\hat\chi)\circ(\chi\circ\varphi)=\hat\varphi\circ[\deg\chi]\circ\varphi=[\deg\chi\deg\varphi]$, and $\deg(\chi\circ\varphi)=\deg\chi\deg\varphi$, so uniqueness of the dual gives the claim. Item 3: $\varphi\circ\hat\varphi=[\deg\varphi]$ and $\deg\hat\varphi=\deg\varphi$, so $\varphi$ is the dual of $\hat\varphi$. Item 4: $[m]\circ[m]=[m^2]=[\deg[m]]$. Item 2 is the one that needs more: Sutherland defers it to the Weil pairing, Silverman proves it through divisors, and Galbraith cites Silverman, Theorem III.6.2. A good expansion adds a page for the Weil pairing's compatibility with duals, or for the additivity of pull-back on $\operatorname{Pic}^0$, and a page for the group structure of the set of isogenies under pointwise addition.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Lemma 9.6.6, Theorem 9.6.27, items 2–4, and Corollary 9.6.28.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 6: Torsion subgroups and endomorphism rings](https://math.mit.edu/classes/18.783/2021/LectureNotes6.pdf), Lemmas 6.10, 6.11 and 6.12.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Theorem 26, items 2, 3 and 5.
