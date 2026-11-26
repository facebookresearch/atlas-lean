# Functions definable in System T are provably total in PA

Every function $f : \mathbb{N}^k \to \mathbb{N}$ that is [definable in System T](functions-definable-in-system-t.md) is
[provably total in Peano arithmetic](provably-total-functions-of-peano-arithmetic.md).

A term $F$ defining $f$ describes an algorithm $t_f$, and proving $\forall \vec x\, \exists y\, t_f(\vec x, y) = 0$ reduces to proving that every application
$F\, \underline{n_1} \cdots \underline{n_k}$ is strongly normalizing; Tait's argument for these terms uses only the finitely many types occurring in $F$ and can be
carried out in PA.

## Depends on

- [Functions definable in System T](functions-definable-in-system-t.md)
- [Provably total functions of Peano arithmetic](provably-total-functions-of-peano-arithmetic.md)

## Proof depends on

- [Strong normalization of System T](strong-normalization-of-system-t.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Proposition 11.6.10 and its proof.
