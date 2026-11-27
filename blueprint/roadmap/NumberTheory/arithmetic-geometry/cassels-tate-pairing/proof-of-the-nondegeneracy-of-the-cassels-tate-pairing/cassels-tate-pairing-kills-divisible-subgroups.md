# The Cassels–Tate pairing kills the divisible subgroups

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, and
$\langle\,,\rangle \colon \text{Ш}(K, A) \times \text{Ш}(K, A^\vee) \to \mathbb{Q}/\mathbb{Z}$ the
[Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md). For an abelian group $M$ let $M_{\mathrm{div}}$ be
its maximal divisible subgroup. Then

$$\langle a, a'\rangle = 0 \quad \text{whenever } a \in \text{Ш}(K, A)_{\mathrm{div}} \text{ or } a' \in \text{Ш}(K, A^\vee)_{\mathrm{div}}.$$

Proof. The groups are torsion. Let $a \in \text{Ш}(K, A)_{\mathrm{div}}$ and let $n \ge 1$ kill $a'$. As $\text{Ш}(K, A)_{\mathrm{div}}$
is divisible, $a = nb$ for some $b \in \text{Ш}(K, A)$, and by biadditivity
$\langle a, a'\rangle = n\langle b, a'\rangle = \langle b, na'\rangle = 0$. The second case is the same with the roles exchanged.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [The Cassels–Tate pairing is biadditive](../construction-of-the-cassels-tate-pairing/biadditivity-of-the-cassels-tate-pairing.md)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, end of the proof of Theorem 6.13 (a), p. 88 ("Note that because the groups are torsion, the pairing must
  kill the divisible subgroups").
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §2, p. 1112 (the maximal divisible subgroup $M_{\mathrm{div}}$).
