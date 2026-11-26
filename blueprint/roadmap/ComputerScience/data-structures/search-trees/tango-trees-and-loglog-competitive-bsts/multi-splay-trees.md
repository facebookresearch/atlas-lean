# Multi-splay trees

There is an online BST, the *multi-splay tree*, that is $O(\log\log n)$-competitive on every access sequence and simultaneously has $O(\log n)$ amortized cost per access, with the same preferred-path structure as tango trees but with each preferred path stored as a splay tree.

## Proof sketch

Replace the red-black auxiliary trees by splay trees, charge the $O(\log\log n)$-competitive analysis to preferred-child changes as for tango trees, and use a splay-style potential over all auxiliary trees to obtain the $O(\log n)$ amortized bound via the access lemma.

## Depends on

- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)
- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)

## Proof depends on

- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)
- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)

## Sources

- Chengwen Chris Wang, Jonathan Derryberry, Daniel Dominic Sleator, "O(log log n)-Competitive Dynamic Binary Search Trees", SODA (2006).
