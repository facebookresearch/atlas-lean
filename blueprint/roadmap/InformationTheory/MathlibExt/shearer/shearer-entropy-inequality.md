---
article_id: af_2316fcdfe37959db6656f636
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.InformationTheory.Shearer.shearer_entropy_inequality
---

# Shearer entropy inequality

Finite Shearer: `k`-cover `C` gives `k * H(full) ≤ ∑_{S∈C} H(S)`.

## Depends on

- [Shearer Full Entropy](shearer-full-entropy.md)
- [Shearer Marginal Entropy](shearer-marginal-entropy.md)

## Proof depends on

- [Shearer entropy inequality general](shearer-entropy-inequality-general.md)

## Sources

- [MathlibExt, MathlibExt.InformationTheory.Shearer](../../../../sources/v2/MathlibExt.md)
- F. R. K. Chung et al., J. Combin. Theory A 43 (1986), DOI 10.1016/0097-3165(86)90019-1. It follows from `shearer_entropy_inequality_general`; the hypothesis `hk` is unused and keeps the source's shape. Proves `Wanted` entry `shearer_entropy_inequality`.
