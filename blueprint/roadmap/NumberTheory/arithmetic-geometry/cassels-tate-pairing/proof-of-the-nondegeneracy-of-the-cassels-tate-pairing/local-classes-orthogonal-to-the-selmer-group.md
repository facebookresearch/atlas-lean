# Local classes orthogonal to the Selmer group

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, $m \ge 1$, and $S$ a
finite set of places of $K$ containing the archimedean places, the places of bad reduction of $A$ and the places above
the primes dividing $m$; $A^\vee$ has good reduction outside $S$ too, the dual of an abelian scheme being one. Let $K_S$, $G_S$, $A_m = A[m](\bar K) \subseteq A(K_S)$ and
$S_S(K, A^\vee)_m = \ker\bigl(H^1(G_S, A^\vee_m) \to \bigoplus_{v \in S} H^1(K_v, A^\vee)\bigr)$ be as in item 4 of
[Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md),
and write $H^0(K_v, A)$ for $A(K_v)$ at the finite places and for the Tate cohomology group $\hat H^0$ at the archimedean
places. For $v \in S$ let

$$\langle\,,\rangle_v \colon H^1(K_v, A_m) \times H^1(K_v, A^\vee_m) \to \mathbb{Q}/\mathbb{Z}, \qquad \langle x, x'\rangle_v = \mathrm{inv}_v(x \cup x'),$$

with the cup product through the pairing $A_m \times A^\vee_m \to \mu_m$ of the Cartier duality of $A[m]$ and $A^\vee[m]$.

**Lemma.** An element $a = (a_v) \in \bigoplus_{v \in S} H^1(K_v, A_m)$ satisfies $\sum_{v \in S} \langle a_v, b'_v\rangle_v = 0$ for all
$b' \in S_S(K, A^\vee)_m$ if and only if $a = a_1 + a_2$ with $a_1$ in the image of the Kummer maps
$\bigoplus_{v \in S} H^0(K_v, A) \to \bigoplus_{v \in S} H^1(K_v, A_m)$ and $a_2$ in the image of the localization
$H^1(G_S, A_m) \to \bigoplus_{v \in S} H^1(K_v, A_m)$.

Milne's proof dualizes the exact sequence $0 \to S_S(K, A^\vee)_m \to H^1(G_S, A^\vee_m) \to \bigoplus_{v \in S} H^1(K_v, A^\vee)$.
By local duality, the dual of $\bigoplus_{v \in S} H^1(K_v, A^\vee_m)$ is $\bigoplus_{v \in S} H^1(K_v, A_m)$, and that of
$\bigoplus_{v \in S} H^1(K_v, A^\vee)$ is $\bigoplus_{v \in S} H^0(K_v, A)$, the dual of the map
$H^1(K_v, A^\vee_m) \to H^1(K_v, A^\vee)$ being the Kummer map of $A$. If $a$ kills $S_S(K, A^\vee)_m$, the image $\gamma^1(a)$
of $a$ in the dual of $H^1(G_S, A^\vee_m)$ is the image of some $b \in \bigoplus_{v \in S} H^0(K_v, A)$; with $a_1$ the
Kummer image of $b$, $a - a_1$ lies in the kernel of $\gamma^1$, which is the image of $H^1(G_S, A_m)$ by the exactness
of the Poitou–Tate sequence at $P^1$. Conversely, Kummer images of $A$ are orthogonal to the classes whose images in
$H^1(K_v, A^\vee)$ vanish, and the image of $H^1(G_S, A_m)$ is orthogonal to that of $H^1(G_S, A^\vee_m)$, by the same
exactness.

## Expansion

This node is still to be broken down. A good expansion states and links:

- at the real places, the compatibility of the duality of
  [Tate local duality for abelian varieties](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/tate-local-duality-for-abelian-varieties.md)
  (its item 4) with the finite-level pairings of $A[m]$ and $A^\vee[m]$ through the Kummer sequences, the analogue of
  its item 3, from the diagram of Milne's Remark I.3.7;
- the dualization of the Selmer sequence and the diagram chase above, with the topologies of the groups, all finite here
  as $S$ is finite.

## Depends on

- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for $G_S$, $A_m$ and $S_S(K, A^\vee)_m$ (its item 4)
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for the Cartier duality of $A[m]$ and $A^\vee[m]$ (its item 3)
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cup products and Tate cohomology

## Proof depends on

- [Poitou–Tate exact sequence](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/poitou-tate-exact-sequence.md), for the exactness at $P^1(G_S, A_m)$ and the maps $\gamma^1$
- [Local Tate duality](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/local-tate-duality.md), for the duality of $H^1(K_v, A_m)$ and $H^1(K_v, A^\vee_m)$ at the finite places
- [Tate duality for the real numbers](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for the real places
- [Tate local duality for abelian varieties](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/tate-local-duality-for-abelian-varieties.md), for the dual of $H^1(K_v, A^\vee)$ and its compatibility with the Kummer maps (its items 2 to 4)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Lemma 6.15 and its proof, pp. 86–87; Theorem 4.10 (b) and the exact sequence after it, pp. 56–57, for the Poitou–Tate sequence; Corollary 3.4,
  p. 43, and Remark 3.7, p. 46, for local duality for abelian varieties.
