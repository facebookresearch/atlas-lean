# A Sigma protocol

A Sigma protocol for a relation $R(x, w)$ between statements $x$ and witnesses $w$ is a three-move
public-coin protocol. The prover, holding $(x, w)$ and random coins $k$, sends a commitment
$a = \mathrm{commit}(x, w, k)$; the verifier sends a uniformly random challenge $e$ from a set
$\mathrm{Ch}$; the prover answers $z = \mathrm{respond}(x, w, k, e)$; and the verifier accepts when
$\mathrm{verify}(x, a, e, z)$ holds. The identification schemes of Katz and Lindell have this shape.

## Sources

- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014, Section 12.5.
- I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010.
