# Homomorphisms of abelian varieties are determined by their action on Tate modules

This node is still to be broken down: the statement is precise, but its proof is not.

Let $A$ and $B$ be [abelian varieties](../../abelian-varieties/abelian-scheme.md) over a field $k$, $k^{\mathrm{sep}}$ a
separable closure of $k$, and $\ell$ a prime different from the characteristic of $k$. Write
$T_\ell A = \varprojlim_n A_{\ell^n}(k^{\mathrm{sep}})$, with multiplication by $\ell$ as transition
maps, and likewise $T_\ell B$; a homomorphism $\alpha \colon A \to B$ induces
$T_\ell \alpha \colon T_\ell A \to T_\ell B$, $(a_n)_n \mapsto (\alpha(a_n))_n$.

1. The map $\operatorname{Hom}(A, B) \to \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, T_\ell B)$,
   $\alpha \mapsto T_\ell \alpha$, is injective.
2. In particular $\operatorname{Hom}(A, B)$ is torsion-free: if $n \alpha = 0$ for an integer
   $n \ge 1$, then $\alpha = 0$.

For 2, $n \, T_\ell \alpha = 0$ forces $T_\ell \alpha = 0$, as $T_\ell B$ is a free
$\mathbb{Z}_\ell$-module (Milne, Remark I.7.3), and 1 applies.

## Expansion

This node is still to be broken down. A good expansion states and links:

- Poincaré's reducibility theorem in Milne's form: there are simple abelian subvarieties
  $A_1, \dots, A_n$ of $A$ such that $(a_1, \dots, a_n) \mapsto a_1 + \dots + a_n$ is an isogeny
  $A_1 \times \dots \times A_n \to A$ (Milne, Proposition I.10.1), a theorem the expansion of the
  [Néron model](../../abelian-varieties/neron-model.md) node also lists;
- that a homomorphism from a simple abelian variety whose kernel is infinite is zero, applied to the
  restriction of $\alpha$ to each $A_i$, whose kernel contains $(A_i)_{\ell^n}(k^{\mathrm{sep}})$ for
  all $n$ when $T_\ell \alpha = 0$ (Milne, proof of Lemma I.10.6);
- the freeness of $T_\ell B$ over $\mathbb{Z}_\ell$, for 2.

## Depends on

- [Abelian scheme](../../abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [Homomorphisms of abelian schemes and commutativity](../../abelian-varieties/homomorphisms-of-abelian-schemes.md), for
  the commutative group $\operatorname{Hom}(A, B)$
- [Isogenies of abelian schemes](../../abelian-varieties/isogenies-of-abelian-schemes.md), for the groups
  $A_{\ell^n}(k^{\mathrm{sep}})$ of $\ell^n$-torsion points
- [Map Linear Map](../../../Algebra/not-yet-classified/tate-module/map-linear-map.md), for the
  $\mathbb{Z}_\ell$-linear map $T_\ell \alpha$ of Tate modules

## Proof depends on

- [Isogenies of abelian schemes](../../abelian-varieties/isogenies-of-abelian-schemes.md), for the
  $\ell^{2gn}$ points of order dividing $\ell^n$ of an abelian variety of dimension $g$ over
  $k^{\mathrm{sep}}$ (its item 3): with them $T_\ell B$ is free over $\mathbb{Z}_\ell$, and when
  $T_\ell \alpha = 0$ the restriction of $\alpha$ to each $A_i$ of positive dimension has an infinite
  kernel

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 7.3, p. 34; Proposition 10.1, p. 42; Lemma 10.6 and its proof, p. 45.
