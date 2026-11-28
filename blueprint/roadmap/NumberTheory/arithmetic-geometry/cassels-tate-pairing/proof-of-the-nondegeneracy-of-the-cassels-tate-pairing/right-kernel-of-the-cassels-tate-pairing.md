# The right kernel of the Cassels–Tate pairing is the divisible subgroup

Let $K$, $A$, $A^\vee$, $\langle\,,\rangle$, $m$ and the $m$-primary parts be as in
[The left kernel of the Cassels–Tate pairing is the divisible subgroup](left-kernel-of-the-cassels-tate-pairing.md). If
$a' \in \text{Ш}(K, A^\vee)(m)$ satisfies $\langle a, a'\rangle = 0$ for all $a \in \text{Ш}(K, A)(m)$, then
$a' \in \text{Ш}(K, A^\vee)(m)_{\mathrm{div}}$.

Proof (Milne). Write $N(B) = \text{Ш}(K, B)(m)/\text{Ш}(K, B)(m)_{\mathrm{div}}$ for an abelian variety $B$ over $K$, a finite group,
and let $R \subseteq \text{Ш}(K, A^\vee)(m)$ be the right kernel, which contains $\text{Ш}(K, A^\vee)(m)_{\mathrm{div}}$ as the pairing kills
divisible subgroups. By the left kernel theorem, the pairing induces a pairing $N(A) \times \text{Ш}(K, A^\vee)(m)/R \to \mathbb{Q}/\mathbb{Z}$
with trivial kernels on both sides; $N(A)$ being finite, so is $\text{Ш}(K, A^\vee)(m)/R$, of the same order. Hence
$\# N(A) = \#\,\text{Ш}(K, A^\vee)(m)/R \le \# N(A^\vee)$. The same argument for $A^\vee$, whose dual is isomorphic to $A$ by
biduality, gives $\# N(A^\vee) \le \# N(A^{\vee\vee}) = \# N(A)$. So all these orders are equal, and
$R = \text{Ш}(K, A^\vee)(m)_{\mathrm{div}}$.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [The left kernel of the Cassels–Tate pairing is the divisible subgroup](left-kernel-of-the-cassels-tate-pairing.md), applied to $A$ and to $A^\vee$
- [The Cassels–Tate pairing kills the divisible subgroups](cassels-tate-pairing-kills-divisible-subgroups.md)
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for the biduality $A \cong A^{\vee\vee}$ (its item 4)
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the finiteness of $N(B)$ (its item 3)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, end of the proof of Theorem 6.13 (a), pp. 88–89 ("Since this holds for all $A$, we also have … It follows
  that all these orders are equal, and therefore that the right kernel is $\text{Ш}(K, A^t)_{m\text{-div}}$").
