# Removing a serial leaves the other table entries unchanged

Let $t$ be a table of
optional Huffman work items. If removing serial number $s$ from $t$ succeeds and returns a tree
together with an updated table $t'$, then for every index $j \ne s$ the entry of $t'$ at $j$
equals the entry of $t$ at $j$ (both are absent when $j$ is out of bounds).
