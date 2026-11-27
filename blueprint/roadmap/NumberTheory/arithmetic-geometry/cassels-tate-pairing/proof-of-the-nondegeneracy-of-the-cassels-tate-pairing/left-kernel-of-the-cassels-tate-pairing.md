# The left kernel of the Cassels–Tate pairing is the divisible subgroup

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, $\langle\,,\rangle$ the
[Cassels–Tate pairing](../construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md), and $m \ge 1$. For an abelian group $M$ let $M(m)$ be
its $m$-primary part, the elements killed by a power of $m$. If $a \in \text{Ш}(K, A)(m)$ satisfies $\langle a, a'\rangle = 0$
for all $a' \in \text{Ш}(K, A^\vee)(m)$, then $a \in \text{Ш}(K, A)(m)_{\mathrm{div}}$, the maximal divisible subgroup of
$\text{Ш}(K, A)(m)$.

Proof (Milne). Choose $S$ as in [Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md);
it serves for every power of $m$, and $\text{Ш}(K, A)(m) = \text{Ш}_S(K, A)(m)$. For $n \ge 1$, consider, with $M = m^n$ in place of
$m$, the diagram with exact rows

$$
\begin{array}{ccccccc}
0 \to & \text{Ш}'(K, A)/M\,\text{Ш}_S(K, A) & \to & \text{Ш}_S(K, A)/M\,\text{Ш}_S(K, A) & \xrightarrow{\ \delta\ } & \text{Ш}^2(G_S, A_M) & \\
 & \downarrow & & \downarrow & & \downarrow & \\
0 \to & \bigl(\text{Ш}(K, A^\vee)[M]/\operatorname{Im} \text{Ш}^1(G_S, A^\vee_M)\bigr)^* & \to & \bigl(\text{Ш}(K, A^\vee)[M]\bigr)^* & \to & \text{Ш}^1(G_S, A^\vee_M)^* &
\end{array}
$$

The top row is the exact sequence of the lemma on elements divisible by $M$ over $G_S$, and the bottom row is the dual of
the exact sequence $\text{Ш}^1(G_S, A^\vee_M) \to \text{Ш}(K, A^\vee)[M] \to \mathrm{Coker} \to 0$. The middle arrow sends $a$ to
$\langle a, \cdot\rangle$, and so does the left arrow, whose image lies in the dual of the cokernel because
$\langle a, a'\rangle = 0$ for $a \in \text{Ш}'(K, A)$ and $a'$ coming from $\text{Ш}^1(G_S, A^\vee_M)$, by the formula for the pairing
on a class divisible by $M$; it is injective by the key lemma. The right arrow is $\eta$ times the Poitou–Tate isomorphism,
and the right square commutes by the comparison of the two pairings. A diagram chase shows that the middle arrow is
injective. So if $a$ is in the left kernel, $a \in m^n\,\text{Ш}_S(K, A)$ for every $n$, hence, projecting to the $m$-primary
part, $a$ is divisible by every power of $m$ in $\text{Ш}(K, A)(m)$. As $\text{Ш}(K, A)(m)$ is the sum of a finite group and a
divisible group, such an element lies in its maximal divisible subgroup.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md), for the choice of $S$
- [Elements of the Shafarevich–Tate group divisible by m over G_S](elements-divisible-by-m-over-g-s.md), for the top row
- [The key lemma: divisibility by m in the Shafarevich–Tate group](key-lemma-on-divisibility-by-m.md), for the injectivity of the left arrow
- [The Cassels–Tate pairing on a class divisible by m](cassels-tate-pairing-on-classes-divisible-by-m.md), for the left arrow
- [The Cassels–Tate pairing and the Poitou–Tate pairing](cassels-tate-and-poitou-tate-pairings.md), for the right square
- [Poitou–Tate duality](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/poitou-tate-duality.md), for the right arrow
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for $\text{Ш}(K, A)(m) = \text{Ш}_S(K, A)(m)$ (its item 4) and the structure of $\text{Ш}(K, A)(\ell)$ (its item 3)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, end of the proof of Theorem 6.13 (a), p. 88 (the diagram, "On passing to the limit over powers of $m$, we
  obtain an injection $\text{Ш}(K, A)^\wedge \to \text{Ш}(K, A^t)(m)^*$. But $\text{Ш}(K, A)^\wedge = \text{Ш}(K, A)/\text{Ш}(K, A)_{m\text{-div}}$, and
  so the left kernel … is $\text{Ш}(K, A)_{m\text{-div}}$"); Remark 6.7, p. 77, for the structure of $\text{Ш}(K, A)(m)$.
