# The Cassels–Tate pairing on a class divisible by m

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, $\langle\,,\rangle$ the
[Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md), and $m \ge 1$. Let $a \in \text{Ш}(K, A)$ and
$a' \in \text{Ш}(K, A^\vee)[m]$, and suppose that $a = ma_1$ for some $a_1 \in H^1(K, A)$. Choose
$t' \in H^1(K, A^\vee[m])$ mapping to $a'$ and, for each place $v$, a class $c_v \in H^1(K_v, A[m])$ mapping to
$a_{1,v} \in H^1(K_v, A)[m]$ under the map induced by $A[m] \subseteq A(\bar K_v)$. Write $c_v \cup t'_v \in \mathrm{Br}(K_v)$
for the cup product through the [Weil pairing](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md)
$e_m$. Then $c_v \cup t'_v$ does not depend on the choice of $c_v$, it vanishes for all but finitely many $v$, and

$$\langle a, a'\rangle = \sum_v \mathrm{inv}_v(c_v \cup t'_v).$$

Proof. Two choices of $c_v$ differ by the Kummer image of a point of $A(K_v)$, and $t'_v$ is the Kummer image of a point
of $A^\vee(K_v)$ because $a'_v = 0$; such cup products vanish. For the $v$ with $a_{1,v} = 0$, all but finitely many,
$c_v$ may be taken to be $0$. For the formula, let $M = mn$ kill $a$, choose a cocycle $\sigma_1 \in Z^1(K, A[mM])$ whose
class maps to $a_1$, and compute $\langle a, a'\rangle$ with $M$, the cocycles $\tau = m\sigma_1$ and $\tau'$ representing $t'$,
and a cochain $\sigma$ with values in $A[M^2]$ and $n\sigma = \sigma_1$, so that $M\sigma = \tau$. As
$e_M(x, x') = e_m(nx, x')$ for $x' \in A^\vee[m]$, $d\sigma \vee_M \tau' = d\sigma_1 \vee_m \tau' = 0$, so $\bar\varepsilon = 0$ serves,
and $\bar\gamma_v = (\sigma_{1,v} - n\rho_v) \vee_m \tau'_v$. Here $\sigma_{1,v} - n\rho_v$ is a cocycle with values in $A[m]$ whose
class maps to $a_{1,v}$, since $n\rho_v = d(nQ_v)$ is a coboundary in $A(\bar K_v)$; so it represents a choice of $c_v$.

Milne's first definition in Proposition I.6.9 takes $c_v$ mapping to $b_{v,1} - b_{1,v}$, whose image in $H^1(K_v, A)$ is
$-a_{1,v}$; it gives $-\langle a, a'\rangle$, and its kernels are the same.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../cassels-tate-pairing-of-an-abelian-variety.md)
- [The Weil pairing through a Poincaré divisor](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md), for the cup product
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the local groups and the Kummer sequences
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)

## Proof depends on

- [The Cassels–Tate pairing does not depend on the choices](../construction-of-the-cassels-tate-pairing/independence-of-the-choices-in-the-cassels-tate-pairing.md)
- [The Cassels–Tate pairing does not depend on m](../construction-of-the-cassels-tate-pairing/independence-of-m-in-the-cassels-tate-pairing.md), for the computation with $M$
- [The Weil pairing is biadditive, Galois-equivariant and compatible in m](../construction-of-the-cassels-tate-pairing/bilinearity-of-the-weil-pairing.md), for $e_M(x, x') = e_m(nx, x')$ (its item 3)
- [The Weil pairing and the Cartier duality of A[m] and its dual](../construction-of-the-cassels-tate-pairing/weil-pairing-and-cartier-duality.md), for the vanishing of the cup product of Kummer images (its item 2)
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the local triviality of $a_1$ at almost all places (its item 1)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, proof of Proposition 6.9, p. 79 ("Suppose first that $a$ is divisible by $m$ in $H^1(G_K, A)$ … We define
  $\langle a, a'\rangle = \sum \mathrm{inv}_v(c_v \cup b'_v)$"), with footnote 14 on the order of $\beta_{v,1}$ and $\beta_{1,v}$ in
  the general case; and the proof of Lemma 6.17, p. 88, which uses this formula.
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, pp. 1143–1144 (the Weil pairing definition, from which the formula is computed).
