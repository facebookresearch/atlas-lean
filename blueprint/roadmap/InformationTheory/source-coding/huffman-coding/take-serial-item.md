# Removing a serial removes one work item from the forest

Let $t$ be a table of optional
Huffman work items, and call the list of work items present in a table its work forest. If
removing serial number $s$ from $t$ succeeds and returns a tree $T$ and an updated table $t'$,
then there is a work item $w$ with tree $T$ and serial number $s$ such that $w$ followed by the
work forest of $t'$ is a permutation of the work forest of $t$.
