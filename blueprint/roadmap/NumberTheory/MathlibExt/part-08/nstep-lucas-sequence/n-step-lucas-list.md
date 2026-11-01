---
article_id: af_d4a216489fb8003be61c2b65
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.nStepLucasList
---

# N Step Lucas List

Finite prefixes of the `n`-step Lucas sequence (source `jis_1628603e2683fb05481e5bfb`,
concept `jis_sem_4e0294575601a2b8a5f0d3d7`): `nStepLucasList n m = [L_1^n, …, L_m^n]`,
where `L_k^n = 2 ^ k - 1` for `1 ≤ k ≤ n` and `L_k^n` is the sum of the previous
`n` terms for `k ≥ n + 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NStepLucasSequence](../../../../../sources/v2/MathlibExt.md)
