---
article_id: af_ff568d38b7f078bd939b80a3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.InformationTheory.Fano.fano_inequality
---

# Fano inequality

Conditional entropy is bounded by error probability via Fano's inequality.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fano inequality general](fano-inequality-general.md)

## Sources

- [MathlibExt, MathlibExt.InformationTheory.Fano](../../../../sources/v2/MathlibExt.md)
- R. M. Fano, Transmission of Information, MIT Press (1961). Proves `Wanted` entry `fano_inequality`. It follows from `fano_inequality_general`; the unused `[DecidableEq β]` keeps the source's shape.
