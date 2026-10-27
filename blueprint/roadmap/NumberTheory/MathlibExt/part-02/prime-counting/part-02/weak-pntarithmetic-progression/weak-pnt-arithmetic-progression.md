---
article_id: af_0dedb06df764191fd1d3e5d1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Chebyshev.weakPNT_arithmeticProgression
---

# Weak PNT arithmetic Progression

For a reduced residue class `a` modulo `q`, the average of the von Mangoldt function over
`n ≡ a (mod q)` tends to `1 / φ(q)`. Source: the proved theorem
`PrimeNumberTheoremAnd.WeakPNT_AP` in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), revision
`be5e07e04cde20c5ceabf63759bd097a9c88173f`, and its use in
[arXiv:2608.24035](https://arxiv.org/abs/2608.24035). Lean preserves the source's natural
representative and half-open `Finset.range` normalization, while omitting the redundant assumption
`1 ≤ q`, which follows from `a < q`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Psi Residue Class](../residue-class-psi/psi-residue-class.md)
- [Tendsto psi Residue Class div self](tendsto-psi-residue-class-div-self.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression](../../../../../../../sources/v2/MathlibExt.md)
