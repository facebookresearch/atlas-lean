# Provably total functions of PA are exactly the System T definable functions

A function $f : \mathbb{N}^k \to \mathbb{N}$ is [provably total in Peano arithmetic](provably-total-functions-of-peano-arithmetic.md) if and only if it is
[definable in System T](functions-definable-in-system-t.md).

One direction is [the provable totality of T-definable functions](system-t-definable-functions-are-provably-total.md). For the other, if
$\mathrm{PA} \vdash \forall x\, \exists y\, t_f(x, y) = 0$, then the same formula is provable in Heyting arithmetic, since provable totality in PA and in HA coincide
(Kreisel); its Dialectica interpretation $\exists y_1^{\mathrm{nat} \to \mathrm{nat}}\, \forall x\, D(y_1 x, x)$ is then realized by a closed term $Y_1$, and
$\lambda x.\, \Pi_2(Y_1 x)$ defines $f$, where $\Pi_2$ defines the second projection of the pairing.

## Depends on

- [Provably total functions of Peano arithmetic](provably-total-functions-of-peano-arithmetic.md)
- [Functions definable in System T](functions-definable-in-system-t.md)

## Proof depends on

- [Functions definable in System T are provably total in PA](system-t-definable-functions-are-provably-total.md)
- [Gödel's Dialectica interpretation of Heyting arithmetic](dialectica-interpretation-of-heyting-arithmetic.md)
- [Closed normal forms of System T](closed-normal-forms-of-system-t.md)
- [Kreisel's theorem on provably total functions](../../../Logic/proof-theory/heyting-arithmetic/kreisel-s-theorem-on-provably-total-functions.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 11.4.2 (Kreisel), Corollary 11.7.6 and Theorem 11.7.7.
