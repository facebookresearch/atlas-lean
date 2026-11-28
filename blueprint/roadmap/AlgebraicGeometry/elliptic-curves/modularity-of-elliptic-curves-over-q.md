# Modularity of elliptic curves over $\mathbb{Q}$

The modularity theorem of Wiles, Taylor–Wiles and Breuil–Conrad–Diamond–Taylor, in the form Darmon states it.

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, and let

$$L(E, s) = \prod_{p \nmid N} (1 - a_p p^{-s} + p^{1-2s})^{-1} \prod_{p \mid N} (1 - a_p p^{-s})^{-1} = \sum_{n \ge 1} a_n n^{-s}$$

be its $L$-function, where $a_p = p + 1 - \#\tilde E(\mathbb{F}_p)$ for the reduction $\tilde E$ of a minimal
Weierstrass model of $E$ at $p$, all of whose points over $\mathbb{F}_p$ are counted, so that $a_p \in \{0, \pm 1\}$
when $p \mid N$; the product converges for $\operatorname{Re}(s) > 3/2$. Then
there is a newform $f = \sum_{n \ge 1} a_n(f) q^n$ of weight $2$ and level $N$, that is, a cusp form of weight $2$ on
$\Gamma_0(N)$ in the new subspace that is an eigenvector of the Hecke operators $T_p$ for the primes $p \nmid N$ and
$U_p$ for the primes $p \mid N$, normalised by $a_1(f) = 1$, such that

$$L(E, s) = L(f, s) = \sum_{n \ge 1} a_n(f) n^{-s},$$

that is, $a_n(f) = a_n$ for every $n \ge 1$. Furthermore, $E$ is isogenous over $\mathbb{Q}$ to the elliptic curve
$E_f$ over $\mathbb{Q}$ that the Eichler–Shimura construction attaches to $f$, the curve with $L(E_f, s) = L(f, s)$:
the abelian variety $A$ of
[Shimura's construction](../../NumberTheory/modular-forms-q-series/modular-forms/shimura-abelian-variety-of-an-eigenform.md)
for $\Gamma = \Gamma_0(N)$ and $f$, of dimension $[\mathbb{Q}(a_n(f) : n \ge 1) : \mathbb{Q}] = 1$ as the $a_n(f) = a_n$
are integers.

## Expansion

This node is still to be broken down. A good expansion states and links:

- newforms and Atkin–Lehner theory, and the Eichler–Shimura construction of $E_f$ (Darmon, §§2.3 and 2.5);
- the $\ell$-adic representations attached to $E$ and to $f$;
- the modularity lifting theorems of Wiles and Taylor–Wiles for semistable curves, proved with Taylor–Wiles patching,
  and their extensions by Diamond, Conrad–Diamond–Taylor and Breuil–Conrad–Diamond–Taylor, which give $f$ with
  $L(E, s) = L(f, s)$ (Darmon, Remark 2.13 and the paragraph after Remark 2.14);
- Faltings' isogeny theorem, which turns the equality of $L$-functions into the isogeny $E \to E_f$.

## Depends on

- [Isogeny of abelian schemes](../abelian-varieties/gaudron-r-mond-isogeny-estimate/is-isogeny.md), for the isogeny over $\mathbb{Q}$ from $E$ to $E_f$
- [Shimura's abelian variety attached to a weight-two eigenform](../../NumberTheory/modular-forms-q-series/modular-forms/shimura-abelian-variety-of-an-eigenform.md), for $E_f$
- [Hecke TLin](../../NumberTheory/not-yet-classified/hecke-operator/hecke-tlin-2.md), for the Hecke operators $T_p$, $p \nmid N$, on cusp forms of weight $2$ for $\Gamma_0(N)$, of which $f$ is an eigenvector
- [Hecke ULin](../../NumberTheory/not-yet-classified/hecke-operator/hecke-ulin-2.md), for the Hecke operators $U_p$, $p \mid N$, on the same space, of which $f$ is an eigenvector

## Proof depends on

- [Galois representations attached to normalized eigenforms](../../NumberTheory/not-yet-classified/exists-galois-rep-charpoly-frob.md), for the $\ell$-adic representations attached to $f$ (Darmon, after Remark 2.14, p. 20): for $f$ of weight $2$ with trivial character, the characteristic polynomial of Frobenius at $p \nmid \ell N$ is $x^2 - a_p(f) x + p$
- [Taylor–Wiles patching datum](../../NumberTheory/modular-forms-q-series/modular-forms/taylor-wiles-patching/patching-datum.md), for the patching data through which the modularity lifting theorems are proved

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 2.12 ("Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$. Then there
  exists a newform $f \in S_2(N)$ such that $L(E, s) = L(f, s)$. Furthermore, $E$ is isogenous to the elliptic curve
  $E_f$ obtained from $f$ via the Eichler-Shimura construction."), Remarks 2.13 and 2.14, p. 20; (1.19), p. 8, for
  $L(E, s)$ and its half-plane of convergence; Corollary 2.9, p. 17, for newforms; Theorem 2.10, p. 18, for $E_f$.
- C. Breuil, B. Conrad, F. Diamond and R. Taylor, *On the modularity of elliptic curves over $\mathbb{Q}$: wild 3-adic
  exercises*, J. Amer. Math. Soc. 14 (2001), no. 4, 843–939; A. Wiles, *Modular elliptic curves and Fermat's last
  theorem*, Ann. of Math. (2) 141 (1995), no. 3, 443–551; R. Taylor and A. Wiles, *Ring-theoretic properties of
  certain Hecke algebras*, Ann. of Math. (2) 141 (1995), no. 3, 553–572. Not read here; cited as Darmon cites them,
  p. 9 and Remark 2.13, p. 20.
