# Power Open Forest Certificate

A reviewable certificate for a scan-produced open PowerSort forest.

`powers` is not inferred from a tree built after the fact: `boundaries`
aligns it with every adjacent pair of open roots and records the exact
transcribed boundary power.  `strict` is the pending-stack heap order, while
`below_left_root` inside `OpenBoundaryCertificate` records the remaining
heap edges into already-built subtrees.
