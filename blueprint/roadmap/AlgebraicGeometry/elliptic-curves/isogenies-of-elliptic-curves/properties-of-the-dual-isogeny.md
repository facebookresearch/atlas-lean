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
- [Dual abelian variety](../../abelian-varieties/dual-abelian-variety.md), its item 3, for the additivity of $f\mapsto f^\vee$
- [The principal polarization of an elliptic curve](../principal-polarization-of-an-elliptic-curve.md), its item 2, for the identification of $E$ with $E^\vee$

## Expansion

Zero cases: in item 1, if $\varphi=0$ or $\chi=0$ then $\chi\circ\varphi=0$ and both sides are $0$ by the convention $\hat0=0$; in item 3, $\varphi=0$ gives $\hat{\hat0}=0$; item 4 for $m=0$ is $\hat0=0$. Otherwise the maps in question are nonzero, where uniqueness of the dual applies. Item 1: $(\hat\varphi\circ\hat\chi)\circ(\chi\circ\varphi)=\hat\varphi\circ[\deg\chi]\circ\varphi=[\deg\chi\deg\varphi]$, and $\deg(\chi\circ\varphi)=\deg\chi\deg\varphi$, so uniqueness of the dual gives the claim. Item 3: $\varphi\circ\hat\varphi=[\deg\varphi]$ and $\deg\hat\varphi=\deg\varphi$, so $\varphi$ is the dual of $\hat\varphi$. Item 4: $[m]\circ[m]=[m^2]=[\deg[m]]$. Item 2 needs more: Sutherland defers it to the Weil pairing, and Galbraith cites Silverman, Theorem III.6.2. Through $\operatorname{Pic}^0$: with $\alpha_E\colon E(\bar k)\to\operatorname{Pic}^0(E_{\bar k})$, $P\mapsto[P]-[O]$, the dual is $\hat\varphi=\alpha_E^{-1}\circ\varphi^*\circ\alpha_{E'}$, with $\varphi^*$ the pull-back of divisor classes (Galbraith, proof of Theorem 9.6.21, in the form given in his errata). The page on the principal polarization identifies each elliptic curve with its dual abelian variety by $P\mapsto$ class of $(-P)-(O)$, which is $-\alpha_E$; the two signs cancel in $\alpha_E^{-1}\circ\varphi^*\circ\alpha_{E'}$, since $\varphi^*$ is a homomorphism, so $\hat\varphi$ corresponds to the dual homomorphism $\varphi^\vee$, which on points is pull-back of line bundles. Additivity of $f\mapsto f^\vee$ on the dual-abelian-variety page then gives item 2. A good expansion adds a page for the formula $\hat\varphi=\alpha_E^{-1}\circ\varphi^*\circ\alpha_{E'}$ and one for the group structure of the set of isogenies under pointwise addition.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Lemma 9.6.6, Theorem 9.6.21 and its proof, Theorem 9.6.27, items 2–4, and Corollary 9.6.28.
- Steven D. Galbraith, [errata to *Mathematics of Public Key Cryptography*](https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html), entry for the proof of Theorem 9.6.21.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 6: Torsion subgroups and endomorphism rings](https://math.mit.edu/classes/18.783/2021/LectureNotes6.pdf), Lemmas 6.10, 6.11 and 6.12.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Theorem 26, items 2, 3 and 5.
