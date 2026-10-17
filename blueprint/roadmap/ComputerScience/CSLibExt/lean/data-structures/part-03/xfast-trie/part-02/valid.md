---
article_id: af_3802ca5bae1e9026ca3b465f
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.YFastTrie.Valid
---

# Valid

The representative trie is a valid x-fast trie whose keys are exactly the
owners of nonempty buckets, stated pointwise (no universe-wide filter),
and every representative is itself a stored key, in its own bucket:
representatives are sampled from the stored keys, so a representative `0`
whose bucket is `{1}` (with `contents = {1}`) is not valid. The classical
bucket ordering invariant (keys of bucket `r` lie in the interval ending
at `r`) is deferred, so this is the y-fast skeleton only.

## Depends on

- [YFast Trie](yfast-trie.md)

## Proof depends on

- [XFast Trie](../part-01/xfast-trie.md)
- [Valid](../part-01/valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.XFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
