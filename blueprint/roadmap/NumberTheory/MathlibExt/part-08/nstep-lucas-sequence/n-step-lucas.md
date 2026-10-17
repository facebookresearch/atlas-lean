---
article_id: af_fb1983e8e9c9ae23e1324a50
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.nStepLucas
---

# N Step Lucas

`n`-step Lucas sequence (source `jis_1628603e2683fb05481e5bfb`, concept
`jis_sem_4e0294575601a2b8a5f0d3d7`): for `n ≥ 1`, `nStepLucas n m = 2 ^ m - 1`
for `1 ≤ m ≤ n` and `nStepLucas n m` is the sum of the `n` preceding values for
`m ≥ n + 1`; by convention `nStepLucas 0 m = 0` for all `m`, and
`nStepLucas n 0 = 0` as the totalization at `m = 0` outside the source domain
`m ≥ 1`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [N Step Lucas List](n-step-lucas-list.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NStepLucasSequence](../../../../../sources/v2/MathlibExt.md)
