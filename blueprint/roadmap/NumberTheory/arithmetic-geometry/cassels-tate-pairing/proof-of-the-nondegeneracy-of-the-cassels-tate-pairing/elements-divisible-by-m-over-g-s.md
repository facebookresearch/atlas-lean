# Elements of the Shafarevich–Tate group divisible by m over G_S

Let $K$, $A$, $m$, $S$, $K_S$, $G_S$ and $A_m$ be as in
[Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md), and let
$\text{Ш}_S(K, A) = \ker\bigl(H^1(G_S, A(K_S)) \to \bigoplus_{v \in S} H^1(K_v, A)\bigr)$, as in item 4 of
[Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md).
Let $\text{Ш}'(K, A)$ be the subgroup of the elements of $\text{Ш}_S(K, A)$ that are divisible by $m$ in
$H^1(G_S, A(K_S))$, and let $\delta \colon H^1(G_S, A(K_S)) \to H^2(G_S, A_m)$ be the connecting map of the Kummer sequence
$0 \to A_m \to A(K_S) \xrightarrow{m} A(K_S) \to 0$. Then $\delta$ maps $\text{Ш}_S(K, A)$ into the Tate–Shafarevich group
$\text{Ш}^2(G_S, A_m) = \ker\bigl(H^2(G_S, A_m) \to \prod_{v \in S} H^2(K_v, A_m)\bigr)$, and the sequence

$$0 \to \text{Ш}'(K, A) \to \text{Ш}_S(K, A) \xrightarrow{\ \delta\ } \text{Ш}^2(G_S, A_m)$$

is exact.

Proof. For $v \in S$ the localization of $\delta(a)$ is the image of $a_v$ under the connecting map of the local Kummer
sequence, which is $0$ for $a \in \text{Ш}_S(K, A)$. By the exactness of the cohomology sequence of the Kummer sequence,
which is exact on $K_S$-points, $\delta(a) = 0$ if and only if $a$ is divisible by $m$ in $H^1(G_S, A(K_S))$.

By item 4 of the Selmer page, the $m$-primary part of $\text{Ш}_S(K, A)$ is that of $\text{Ш}(K, A)$, so the lemma concerns
the elements of $\text{Ш}(K, A)(m)$ that become divisible by $m$ over $G_S$.

## Depends on

- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for $G_S$, $A_m$ and $\text{Ш}_S(K, A)$ (its item 4)
- [Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md), for the choice of $S$ and the notation $K_S$, $G_S$, $A_m$
- [Tate–Shafarevich groups of Galois modules](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/tate-shafarevich-groups.md), for $\text{Ш}^2(G_S, A_m)$
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the connecting maps

## Proof depends on

- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the surjectivity of multiplication by $m$ on $A(K_S)$ (its item 4)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the long exact cohomology sequence and its compatibility with restriction

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Lemma 6.16 and its proof, p. 87 (stated for "the subgroup of $\text{Ш}(K, A)$ of elements that become
  divisible by $m$ in $H^1(G_S, A)$"; the lower right group of its diagram should be $\bigoplus_{v \in S} H^2(K_v, A_m)$);
  Corollary 6.6, p. 76, for the independence of $S$.
