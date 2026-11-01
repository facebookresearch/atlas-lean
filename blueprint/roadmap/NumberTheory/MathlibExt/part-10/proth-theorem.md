---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.proth_theorem
---

# Proth Theorem

Proth's theorem (Proth primality criterion via quadratic nonresidue witness):
a Proth number `N = h * 2 ^ k + 1` with `h` odd and `h < 2 ^ k` is prime
if and only if there exists `a` with `a ^ ((N - 1) / 2) = -1` in `ZMod N`.

Proof: The forward implication uses a nonsquare and Euler's criterion; the reverse uses Proth's
least-prime-factor order argument. Sources: Proth (1878), p. 926, and the Wikipedia exposition.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ProthTheorem](../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Proth%27s_theorem
