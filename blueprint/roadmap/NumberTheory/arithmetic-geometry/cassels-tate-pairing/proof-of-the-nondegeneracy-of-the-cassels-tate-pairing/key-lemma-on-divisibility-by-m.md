# The key lemma: divisibility by m in the Shafarevich–Tate group

Let $K$, $A$, $A^\vee$, $m$, $S$ and $G_S$ be as in
[Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md), let $\langle\,,\rangle$ be the
[Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md), and let $\text{Ш}_S(K, A) \supseteq \text{Ш}'(K, A)$ be as
in [Elements of the Shafarevich–Tate group divisible by m over G_S](elements-divisible-by-m-over-g-s.md), regarded inside
$\text{Ш}(K, A)$ by inflation. For $a \in \text{Ш}'(K, A)$,

$$a \in m\,\text{Ш}_S(K, A) \iff \langle a, a'\rangle = 0 \text{ for all } a' \in \text{Ш}(K, A^\vee)[m].$$

Proof. If $a = ma_0$, then $\langle a, a'\rangle = \langle a_0, ma'\rangle = 0$. Conversely, let $a_1 \in H^1(G_S, A(K_S))$ with
$ma_1 = a$. At $v \notin S$, $a_{1,v} = 0$, as $a_1$ is unramified there and $A$ has good reduction; for $v \in S$ choose
$c_v \in H^1(K_v, A_m)$ mapping to $a_{1,v}$. If some $b_0 \in H^1(G_S, A_m)$ has $b_{0,v} - c_v$ in the image of the Kummer
map of $A(K_v)$ for all $v \in S$, its image $a_0$ in $H^1(G_S, A(K_S))$ has $a_{0,v} = a_{1,v}$, so $a_1 - a_0 \in \text{Ш}_S(K, A)$
and $m(a_1 - a_0) = a$. By the lemma on local classes orthogonal to the Selmer group, such a $b_0$ exists if and only if
$\sum_{v \in S} \langle c_v, b'_v\rangle_v = 0$ for all $b' \in S_S(K, A^\vee)_m$. By the comparison of the Weil pairing with
the Cartier duality pairing and the formula for the pairing on a class divisible by $m$, applied with $t'$ the class of
$b'$ in $H^1(K, A^\vee[m])$ and $c_v = 0$ for $v \notin S$, this sum is $\pm\langle a, a'\rangle$, where $a'$ is the image of $b'$
in $\text{Ш}(K, A^\vee)[m]$; and every element of $\text{Ш}(K, A^\vee)[m]$ is such an image, by the Selmer sequence.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../cassels-tate-pairing-of-an-abelian-variety.md)
- [Elements of the Shafarevich–Tate group divisible by m over G_S](elements-divisible-by-m-over-g-s.md), for $\text{Ш}_S(K, A)$ and $\text{Ш}'(K, A)$

## Proof depends on

- [Local classes orthogonal to the Selmer group](local-classes-orthogonal-to-the-selmer-group.md)
- [The Cassels–Tate pairing on a class divisible by m](cassels-tate-pairing-on-classes-divisible-by-m.md)
- [The Weil pairing and the Cartier duality of A[m] and its dual](../construction-of-the-cassels-tate-pairing/weil-pairing-and-cartier-duality.md), for the sign between the two cup products (its item 1)
- [The Cassels–Tate pairing is biadditive](../construction-of-the-cassels-tate-pairing/biadditivity-of-the-cassels-tate-pairing.md)
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the Selmer sequence (its item 2), the passage to $G_S$ (its item 4), applied also to $A^\vee$, and the vanishing of $a_{1,v}$ outside $S$ (its item 5)
- [Dual abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-scheme.md), for the good reduction of $A^\vee$ outside $S$, needed to apply item 4 of the Selmer page to $A^\vee$

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Lemma 6.17 and its proof, pp. 87–88. The proof refers to "(6.14)" and to "$S_S(K, A)_m$" where it uses Lemma
  6.15 and $S_S(K, A^t)_m$, and writes $a_1 + a_0$ and $m(a_1 - a_0)$ for the same element; the signs here follow the
  formula for the pairing on a class divisible by $m$.
