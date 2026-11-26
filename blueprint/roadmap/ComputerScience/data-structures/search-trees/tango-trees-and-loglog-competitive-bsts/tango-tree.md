# Tango trees

A *tango tree* represents each preferred path of the reference tree $P$ by an *auxiliary tree*: a red-black tree keyed by the path's keys and augmented at every node with its depth in $P$ and the minimum and maximum depth in its subtree. The auxiliary trees are linked into a single BST on $[n]$ by hanging the auxiliary tree of each path below the node of the auxiliary tree of its parent path at which a search for its keys leaves. An access to $x$ walks down, and every time the preferred child of some node of $P$ changes, it *cuts* the corresponding auxiliary tree at a depth and *joins* it with another, using red-black split and concatenate operations.

## Depends on

- [Preferred children and preferred paths](preferred-paths.md)
- [Splicing two red-black trees](../red-black-tree/join.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
