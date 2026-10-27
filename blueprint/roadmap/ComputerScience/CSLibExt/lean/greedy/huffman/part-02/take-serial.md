---
article_id: af_3e56fbeef9f96a734cbc951e
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.takeSerial?
---

# Take Serial?

Remove the work item with a given serial number. The table is indexed
directly by serial, so this is one indexed lookup and one indexed update
rather than a scan of the work forest.

## Depends on

- [Huffman Tree](../part-01/huffman-tree.md)
- [Huffman Work Item](huffman-work-item.md)

## Proof depends on

- [Huffman Priority](huffman-priority.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.Huffman](../../../../../../../sources/v2/CSLibExt.md)
