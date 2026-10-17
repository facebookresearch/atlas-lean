---
article_id: af_99767731cb627ea0ac40ec49
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.YFastTrie.contents
---

# Contents

All stored keys: the union of the representatives' buckets. Computed
from `reps.contents` (sparse), not by filtering the `2 ^ w`-element key
universe against an existential over all potential owners.

## Depends on

- [YFast Trie](yfast-trie.md)

## Proof depends on

- [XFast Trie](../part-01/xfast-trie.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.XFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
