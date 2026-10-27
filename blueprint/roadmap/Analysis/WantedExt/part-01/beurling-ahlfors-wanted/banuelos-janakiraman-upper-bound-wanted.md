---
article_id: af_5d9dbc82ddeff78cd4bd0ef3
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.BeurlingAhlforsWanted.banuelosJanakiramanUpperBound_wanted
---

# Banuelos Janakiraman Upper Bound wanted

Source: Bañuelos and Janakiraman, *Lp-bounds for the
Beurling--Ahlfors transform*, Trans. Amer. Math. Soc. 360 (2008):
`‖B‖ₚ ≤ 1.575 (p* - 1)` for all `1 < p`. Stated as the actual finite
exponential bound (an admissible `L^p` bound constant), not as an
inequality for the totalized infimum; combined with
`beurlingNorm_le_of_isBound` (and `0 ≤ 1.575 * (pstar p - 1)`, from
`two_le_pstar`) it yields `beurlingNorm p ≤ 1.575 * (pstar p - 1)`.
Known literature result; its proof is not supplied here.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.BeurlingAhlforsWanted](../../../../../sources/v2/WantedExt.md)
