# Sequential access in splay trees takes linear time

For every initial splay tree on $n$ keys, accessing all keys in increasing order $1, 2, \dots, n$ by splaying costs $O(n)$ rotations in total.

## Proof sketch

Tarjan bounds the number of rotations by tracking the right spine of the tree: each zig-zig step at the left end of the tree removes nodes from the left path permanently, and a careful counting of zig-zag and zig-zig steps shows that every node participates in $O(1)$ amortized rotations over the whole sweep.

## Depends on

- [Splay operation](../splay-tree/splay.md)

## Sources

- Robert E. Tarjan, "Sequential Access in Splay Trees Takes Linear Time", Combinatorica 5(4) (1985).
