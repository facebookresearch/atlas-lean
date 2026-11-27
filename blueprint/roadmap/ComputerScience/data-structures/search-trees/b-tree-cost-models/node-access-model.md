# Node-access (page-read) model for B-trees

In the *node-access model*, a tree is stored in an external store and accessed only through handles: a query program receives a root handle (or an empty marker) and may issue $\mathrm{readNode}(h)$, which returns the keys, values and child handles of the node $h$ (a page); scanning a page in memory is free, and the cost is the number of page reads. A store *denotes* a tree if reading from the root handle unfolds to that tree. For order-statistic queries the page may additionally record the entry count of each child subtree.

## Depends on

- [The external-memory model](../../../memory-hierarchy-algorithms/external-memory-algorithms/the-external-memory-model.md)
- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Sources

- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
- A. Aggarwal and J. S. Vitter, "The Input/Output Complexity of Sorting and Related Problems", Communications of the ACM 31(9), pp. 1116-1127, 1988.
- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
