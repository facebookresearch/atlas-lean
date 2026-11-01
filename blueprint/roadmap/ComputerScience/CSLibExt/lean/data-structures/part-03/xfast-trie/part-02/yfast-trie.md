---
article_id: af_d50eb4bd86eaf5b7295a06ee
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.YFastTrie
---

# YFast Trie

The y-fast skeleton: an x-fast trie of representative keys, with a bucket of keys per
potential representative. In the classical structure each bucket is a balanced search
tree of Θ(w) keys; here buckets are `Finset`s, and the ordering invariant and split/merge
maintenance are deferred (see the module documentation). No complexity bound is claimed.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.XFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
