# Potential good reduction of abelian varieties with complex multiplication

A **CM field** is a totally imaginary quadratic extension $E$ of a totally real number field; it has
an involution $\iota \ne 1$ such that complex conjugation acts on $\sigma(E)$ as
$\sigma \iota \sigma^{-1}$ for every embedding $\sigma \colon E \to \mathbb{C}$. An
[abelian variety](abelian-scheme.md) $A$ over $\mathbb{C}$ has **complex multiplication** by $E$ if
$E \subset \operatorname{End}(A) \otimes \mathbb{Q}$, $2 \dim A = [E : \mathbb{Q}]$, and for some
[polarization](polarization.md) $\lambda$ of $A$ the Rosati involution
$\alpha \mapsto \lambda^{-1} \circ \alpha^\vee \circ \lambda$ of $\operatorname{End}(A) \otimes \mathbb{Q}$
stabilizes $E$ and acts on it as $\iota$.

An abelian variety over a nonarchimedean local field $F$, the fraction field of a complete discrete
valuation ring $R$, has **good reduction** if it has a projective embedding whose reduction modulo the
maximal ideal of $R$ (the variety over the residue field cut out by the reductions of the equations
with coefficients in $R$) is nonsingular; an abelian variety over a number field $k$ has good
reduction at a finite prime $v$ of $k$ if it has good reduction over the completion $k_v$.

**Theorem.** Let $A$ be an abelian variety over $\mathbb{C}$ with complex multiplication by a CM field
$E$. Then $A$ has a model over some number field $k \subset \mathbb{C}$, and after replacing $k$ by a
larger number field the model has good reduction at every finite prime of $k$.

Milne states the theorem without proof. The potential good reduction is due to Serre and Tate, who
obtain it from their criterion for potential good reduction in terms of the action of inertia on the
Tate modules, a consequence of the existence of [Néron models](neron-model.md).

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties
- [Polarization](polarization.md), for the Rosati involution
- [Dual abelian variety](dual-abelian-variety.md), for the dual homomorphism $\alpha^\vee$

## Proof depends on

- [Néron model of an abelian variety](neron-model.md), for the Néron–Ogg–Shafarevich criterion and the
  action of inertia on Tate modules

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter II, §2, pp. 81–82 (CM fields, abelian
  varieties with complex multiplication, good reduction) and Proposition 2.10 (stated with "Proof.
  Omitted."); Chapter I, §14 (the Rosati involution).
- J.-P. Serre and J. Tate, "Good reduction of abelian varieties", Ann. of Math. (2) 88 (1968),
  492–517.
