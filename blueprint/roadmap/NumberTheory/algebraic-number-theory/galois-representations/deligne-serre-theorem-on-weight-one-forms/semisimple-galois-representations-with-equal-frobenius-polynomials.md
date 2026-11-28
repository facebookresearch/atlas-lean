# Semisimple Galois representations with the same Frobenius polynomials are isomorphic

Let $G = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with its Krull topology, and let $k$ be either $\mathbb{C}$ or a
finite field, each with the discrete topology, or a finite extension of $\mathbb{Q}_\ell$ for a prime $\ell$, with its
natural topology. A linear representation of $G$ is a continuous homomorphism $\rho \colon G \to \mathrm{GL}_n(k)$. It is
unramified at a prime $p$ if it is trivial on the inertia group of a place of $\overline{\mathbb{Q}}$ above $p$; then
$F_{\rho,p}$ denotes the image under $\rho$ of the Frobenius substitution at that place, in Artin's convention (the
arithmetic Frobenius, whose inverse is the geometric Frobenius), well defined up to conjugation, and

$$P_{\rho,p}(T) = \det(1 - F_{\rho,p} T).$$

Let $X$ be a set of primes of Dirichlet density $1$, and let $\rho, \rho' \colon G \to \mathrm{GL}_n(k)$ be semisimple linear
representations. Suppose that for every $p \in X$ both $\rho$ and $\rho'$ are unramified at $p$ and
$P_{\rho,p}(T) = P_{\rho',p}(T)$, or, when $k$ has characteristic $0$, only $\operatorname{Tr}(F_{\rho,p}) = \operatorname{Tr}(F_{\rho',p})$.
Then $\rho$ and $\rho'$ are isomorphic.

This is Lemme 3.2 of Deligne–Serre. They do not say which density they mean; the proof uses only that $X$ meets every
set of primes that the [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md) gives
positive Dirichlet density, and they apply the lemma with $X$ the set of primes not dividing a given integer $N$
(Remarque 3.3). When $k = \mathbb{C}$ every linear representation has finite image, so semisimplicity is automatic
(Remarque 3.4).

## Depends on

- [Frobenius conjugacy class](../../../../RingTheory/ramification/frobenius-elements/conjugacy-class-of-the-arithmetic-frobenius-at-a/arith-frob-conj-class.md), for the arithmetic Frobenius elements

## Proof depends on

- [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md), applied to the finite Galois extensions of $\mathbb{Q}$ cut out by the open normal subgroups of $G$, so that the Frobenius elements of the primes in $X$ are dense in $G$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the theorem that a semisimple linear representation of a group is determined up to isomorphism by its
  characteristic polynomials, and in characteristic $0$ by its traces (Curtis–Reiner, §30.16 and th. 30.16, as cited in
  Deligne–Serre (1974), pp. 513 and 523);
- the continuity of $g \mapsto \det(1 - \rho(g)T)$ on $G$, which with the density of the Frobenius elements gives equal
  characteristic polynomials (or traces) at every element of $G$.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §3.1 and (3.1.1), pp. 512–513, with footnote (1),
  p. 513, for Artin's convention; Lemme 3.2 and its proof, p. 513 ("Soit X un ensemble de nombres premiers de densité
  1 et soient ρ et ρ′ deux représentations linéaires semi-simples de G"); Remarques 3.3 and 3.4, p. 513.
- C. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*, Interscience, New York
  (1962), §30.16, as cited in Deligne–Serre (1974), pp. 513 and 523; not read.
