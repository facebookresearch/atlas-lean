---
article_id: af_889b854bbb9ec03599747ff2
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.ComplexityTheory.NP
---

# NP

The class NP: decision problems with a polynomial bound `p` and a poly-time
verifier `R` such that `L x` iff some witness `w` of length at most `p |x|` is
accepted. Inlined from FormalConjectures (absent from Mathlib).

## Depends on

- [Decision Complexity Class](decision-complexity-class.md)

## Proof depends on

- [Bitstring Encoding](bitstring-encoding.md)
- [Bit Decode](bit-decode.md)
- [Bit Decode bit Encode](bit-decode-bit-encode.md)
- [Bit Encode](bit-encode.md)
- [Delimit](delimit.md)
- [Undelimit](undelimit.md)
- [Undelimit Blocks](undelimit-blocks.md)
- [Undelimit Blocks Aux](undelimit-blocks-aux.md)
- [Decision Problem](decision-problem.md)
- [Is Poly Time](is-poly-time.md)

## Sources

- [MathlibExt, MathlibExt.Computability.Complexity](../../../../sources/v2/MathlibExt.md)
