# Potential good reduction of abelian varieties with complex multiplication

This node is still to be broken down: the statement is precise, but its proof is not.

A **CM field** is a totally imaginary quadratic extension $E$ of a totally real number field; it has
an involution $\iota \ne 1$ such that complex conjugation acts on $\sigma(E)$ as $\sigma \iota
\sigma^{-1}$ for every embedding $\sigma \colon E \to \mathbb{C}$. An
[abelian variety](../abelian-scheme.md) $A$ over $\mathbb{C}$ has **complex multiplication** by $E$ if
$E \subset \operatorname{End}(A) \otimes \mathbb{Q}$, $2 \dim A = [E : \mathbb{Q}]$, and for some
[polarization](../polarization.md) $\lambda$ of $A$ the Rosati involution $\alpha \mapsto \lambda^{-1}
\circ \alpha^\vee \circ \lambda$ of $\operatorname{End}(A) \otimes \mathbb{Q}$, with $\alpha^\vee$
the [dual homomorphism](../dual-abelian-variety.md), stabilizes $E$ and acts on it as $\iota$.

An abelian variety $A$ over the fraction field $K$ of a discrete valuation ring $R$ has **good
reduction** if it is the generic fibre of an abelian scheme over $R$ (Milne's notes on complex
multiplication). His notes on abelian varieties phrase it through a projective embedding: the
reduction is the special fibre of the scheme-theoretic closure of $A$ in projective space over $R$,
defined by the homogeneous ideal of $A$ contracted to $R[X_0, \dots, X_n]$, and it should be
nonsingular, not merely cut out by some choice of scaled equations. An abelian variety over a number
field $k$ has good reduction at a finite prime $v$ of $k$ if it has good reduction over the local
ring of $v$, equivalently over its completion.

**Theorem.** Let $A$ be an abelian variety over $\mathbb{C}$ with complex multiplication by a CM
field $E$. Then $A$ has a model over some number field $k \subset \mathbb{C}$, and after replacing
$k$ by a larger number field the model has good reduction at every finite prime of $k$.

Milne's notes on abelian varieties state the theorem without proof. A good expansion follows his
notes on complex multiplication and has pages for: the full faithfulness of extension of scalars
from $\bar{\mathbb{Q}}$ to $\mathbb{C}$ and the descent of abelian varieties with complex
multiplication to $\bar{\mathbb{Q}}$, hence to a number field, together with the endomorphisms
(Proposition 7.9); the [Néron–Ogg–Shafarevich criterion](../neron-model.md) and its consequence that an
abelian variety over a local field whose $\ell$-adic Galois image is commutative, for some $\ell$
different from the residue characteristic, has potential good reduction (Theorem 6.12, Corollary
6.13); the commutativity of the $\ell$-adic image for an abelian variety with complex multiplication
defined over $k$, whose endomorphisms are all defined over $k$, giving potential good reduction at
every finite prime (Proposition 7.12); and the passage from potential good reduction at each prime
to one finite extension good at all of them: good reduction away from a finite set of primes, and
one finite extension that kills the finite images of inertia at the remaining primes simultaneously,
for instance a field of definition of the $\ell^m$-torsion points, with $\ell$ different from every
residue characteristic of the remaining primes and $\ell^m \ge 3$, so that the $\ell^m$-torsion
detects their finite images of inertia (an automorphism of finite order of the Tate module that is
trivial on the $\ell^m$-torsion is trivial when $\ell^m \ge 3$).

## Depends on

- [Abelian scheme](../abelian-scheme.md), for abelian varieties and abelian schemes
- [Polarization](../polarization.md), for the Rosati involution
- [Dual abelian variety](../dual-abelian-variety.md), for the dual homomorphism $\alpha^\vee$

## Proof depends on

- [Néron model of an abelian variety](../neron-model.md), for the Néron–Ogg–Shafarevich criterion and the
  action of inertia on Tate modules

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter II, §2, pp. 81–82 (CM fields, abelian
  varieties with complex multiplication, good reduction through the closure of a projective
  embedding) and Proposition 2.10 (stated with "Proof. Omitted."); Chapter I, §14 (the Rosati
  involution).
- J. S. Milne, *Complex Multiplication*, course notes,
  <https://www.jmilne.org/math/CourseNotes/CM.pdf>: Chapter II, the definition of good reduction,
  Theorem 6.12 and Corollary 6.13; Proposition 7.9 and Proposition 7.12 with their proofs.
- J.-P. Serre and J. Tate, "Good reduction of abelian varieties", Ann. of Math. (2) 88 (1968),
  492–517.
