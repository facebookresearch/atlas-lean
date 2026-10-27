---
article_id: af_db943f5f7b2ef5c7be168b6d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.takagiEll_zero
---

# Takagi Ell zero

Defining equation of `takagiEll` at the padded index `0` (required clause `ell`):
the auxiliary base value `takagiEll n k 0` is `0`. This is not the source value
`ell_1`, which is `takagiEll n k 1` and is covered by `takagiEll_one`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`.

## Depends on

- [Takagi Ell](takagi-ell.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.TakagiFunction](../../../../../../../sources/v2/MathlibExt.md)
