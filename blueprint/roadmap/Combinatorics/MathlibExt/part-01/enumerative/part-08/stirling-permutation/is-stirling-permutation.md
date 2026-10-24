---
article_id: af_8c9bd095c4d42ed6b115f17a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsStirlingPermutation
---

# Is Stirling Permutation

Stirling permutation of order `n` (concept `jis_sem_2caeda2867f94a2afc83e068`,
statement `jis_e248733f0c7bd4348abb29fb`,
source `https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.tex`):
a word `w : Fin (2 * n) → ℕ` with values in `{1, …, n}`, each value occurring
exactly twice, such that every value appearing between the two instances of `i`
is strictly greater than `i`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.StirlingPermutation](../../../../../../../sources/v2/MathlibExt.md)
