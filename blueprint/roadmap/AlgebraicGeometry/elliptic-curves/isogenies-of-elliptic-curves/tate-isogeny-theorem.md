# Tate's isogeny theorem for elliptic curves over finite fields

Two elliptic curves over a finite field are isogenous over that field exactly when they have the same number of rational points.

Let $\mathbb{F}_q$ be a finite field and $E$, $E'$ elliptic curves over $\mathbb{F}_q$. Then there is a nonzero [isogeny](isogeny-of-elliptic-curves.md) $E\to E'$ defined over $\mathbb{F}_q$ if and only if

$$
\#E(\mathbb{F}_q)=\#E'(\mathbb{F}_q),
$$

equivalently if and only if their [Frobenius traces](../point-counts-and-frobenius-traces/frobenius-trace.md) $a_q=q+1-\#E(\mathbb{F}_q)$ agree.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)
- [Frobenius trace](../point-counts-and-frobenius-traces/frobenius-trace.md)

## Proof depends on

- [The kernel of an isogeny has order its separable degree](kernel-order-equals-separable-degree.md)
- [Degrees of isogenies multiply under composition](degree-is-multiplicative.md)

## Expansion

Only if (Galbraith, Theorem 9.7.4): $E(\mathbb{F}_q)=\ker(\pi_q-1)$ for the $q$-power Frobenius $\pi_q$, and $\pi_q-1$ is separable, so $\#E(\mathbb{F}_q)=\deg(\pi_q-1)$. An isogeny $\varphi$ over $\mathbb{F}_q$ satisfies $\pi'_q\circ\varphi=\varphi\circ\pi_q$, hence $(\pi'_q-1)\circ\varphi=\varphi\circ(\pi_q-1)$, and multiplicativity of degrees gives $\deg(\pi'_q-1)=\deg(\pi_q-1)$. The converse is Tate's theorem (1966), proved through the action of Frobenius on Tate modules, or for elliptic curves through complex multiplication; none of the sources used here proves it. A good expansion adds pages for the separability of $\pi_q-1$, for Tate modules and the injectivity of $\operatorname{Hom}(E,E')\otimes\mathbb{Z}_\ell\to\operatorname{Hom}(T_\ell E,T_\ell E')$, and for Tate's theorem on the image.

De Feo states this theorem as his Theorem 13 under the name Sato–Tate; it is Tate's isogeny theorem, as Galbraith names it. The separability of $\pi_q-1$ used above is Galbraith, Corollary 9.7.3 ($m+n\pi_q$ is separable exactly when $m$ is prime to $q$).

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Corollary 9.7.3, Theorem 9.7.4 and the paragraph after it.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), opening paragraph of Section 25.3.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Theorem 13.
