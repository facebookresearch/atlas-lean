# Guide tree merger for disjoint tree merging

Divide-and-conquer species-tree pipelines split the taxa into disjoint subsets using a starting tree, estimate a tree on each subset, and then merge the leaf-disjoint subset trees into one tree. Choosing the merged tree closest to a guide tree is NP-hard in general but polynomial when subset trees may only be joined by new edges ("unblended" merging), and the resulting pipeline inherits statistical consistency from its components.

- [Unblended disjoint tree merging with a guide tree](unblended-disjoint-tree-merging-with-a-guide-tree.md)
