# The Cassels–Tate pairing and the Poitou–Tate pairing

Let $K$, $A$, $A^\vee$, $m$, $S$, $G_S$, $A_m$ and $A^\vee_m$ be as in
[Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md), with $A^\vee_m$ identified
with $\operatorname{Hom}(A_m, \mu_m)$ by the Cartier duality pairing, and let $\text{Ш}_S(K, A)$ and
$\delta \colon \text{Ш}_S(K, A) \to \text{Ш}^2(G_S, A_m)$ be as in
[Elements of the Shafarevich–Tate group divisible by m over G_S](elements-divisible-by-m-over-g-s.md). Let
$(\,,)_{PT} \colon \text{Ш}^2(G_S, A_m) \times \text{Ш}^1(G_S, A^\vee_m) \to \mathbb{Q}/\mathbb{Z}$ be the perfect pairing of
[Poitou–Tate duality](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/poitou-tate-duality.md).
A class $b' \in \text{Ш}^1(G_S, A^\vee_m)$ maps to an element $a'$ of $\text{Ш}(K, A^\vee)[m]$, its image in
$H^1(G_S, A^\vee(K_S))$, which is locally trivial at $S$ and, by good reduction, outside $S$.

**Theorem.** There is a sign $\eta \in \{1, -1\}$ such that for all $a \in \text{Ш}_S(K, A)$ and $b' \in \text{Ш}^1(G_S, A^\vee_m)$,
with $a'$ the image of $b'$ and $\langle\,,\rangle$ the [Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md),

$$\langle a, a'\rangle = \eta\,(\delta(a), b')_{PT}.$$

This is the commutativity, up to sign, of the right-hand square of the diagram in Milne's proof of Theorem I.6.13 (a),
whose third vertical arrow is the Poitou–Tate isomorphism $\text{Ш}^2_S(K, A_m) \to \text{Ш}^1_S(K, A^t_m)^*$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- a description of $(\,,)_{PT}$ by cochains: for $x \in \text{Ш}^2(G_S, A_m)$ and $y \in \text{Ш}^1(G_S, A^\vee_m)$, local
  cochains trivializing $x$ and $y$ at the places of $S$, a global cochain trivializing the cup product, and the sum of
  the local invariants, with its comparison with the definition through the $S$-idèle class formation;
- the computation of $\langle a, a'\rangle$ with a cocycle $\tau'$ representing $b'$, locally a coboundary at the places of $S$,
  and with $\delta(a)$ represented by $d\sigma$ for a lift $\sigma$ of a cocycle of $a$, which identifies the two cochain
  expressions up to sign;
- the comparison of the Weil pairing with the Cartier duality pairing, for the sign.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../cassels-tate-pairing-of-an-abelian-variety.md)
- [Poitou–Tate duality](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/poitou-tate-duality.md)
- [Elements of the Shafarevich–Tate group divisible by m over G_S](elements-divisible-by-m-over-g-s.md), for $\delta$
- [Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md), for $S$ and the notation $G_S$, $A_m$, $A^\vee_m$
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the local triviality of $a'$ outside $S$ (its item 5, applied to $A^\vee$)
- [Dual abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-scheme.md), for the good reduction of $A^\vee$ outside $S$

## Proof depends on

- [The Weil pairing and the Cartier duality of A[m] and its dual](../construction-of-the-cassels-tate-pairing/weil-pairing-and-cartier-duality.md), for the sign (its item 1)
- [The Cassels–Tate pairing does not depend on the choices](../construction-of-the-cassels-tate-pairing/independence-of-the-choices-in-the-cassels-tate-pairing.md)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, end of the proof of Theorem 6.13 (a), p. 88 (the diagram, whose "third vertical arrow is the isomorphism
  of (4.10)", and "A diagram chase now shows that the middle vertical arrow is also injective"); Theorem 4.10 (a), pp. 56–57,
  for the Poitou–Tate duality of $\text{Ш}^1$ and $\text{Ш}^2$.
