# Sequential access in splay trees takes linear time

For every initial splay tree on $n$ keys, accessing all keys in increasing order $1, 2, \dots, n$ by splaying costs $O(n)$ rotations in total.

## Proof sketch

The potential-function analysis of splaying gives only $O(n \log n)$ for this sequence. Tarjan instead bounds the total number of rotations by a direct combinatorial counting argument over the rotations performed during the sweep.

## Depends on

- [Splay operation](../splay-tree/splay.md)

## Sources

- Robert E. Tarjan, "Sequential Access in Splay Trees Takes Linear Time", Combinatorica 5(4) (1985).
