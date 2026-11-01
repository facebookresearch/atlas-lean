---
article_id: af_ebb46268c5a23ff6e069df0b
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.cloitreApprox
---

# Cloitre Approx

Paperfolding approximants: `A_0 = [1, 1]`, `A_{k+1} = A_k ++ (A_k)^r`.

Unrolls as `A_0 = [1, 1]`, `A_1 = [1, 1, 2]`,
`A_2 = [1, 1, 2, 1, 1, 1, 1]`,
`A_3 = [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1]`, continuing `2, 2, …`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cloitre Mirror](cloitre-mirror.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.CloitreSequence](../../../../../../sources/v2/MathlibExt.md)
