# RowDiff sparsification of de Bruijn graph annotations

Annotated de Bruijn graphs index large sequence collections by attaching to each $k$-mer the set of samples or labels containing it. Adjacent $k$-mers usually carry nearly identical label sets, so replacing each annotation row by its XOR with a successor's row, while keeping enough anchor rows to undo the transform, sparsifies the annotation matrix losslessly.

- [RowDiff transform and its anchor conditions](rowdiff-transform-and-anchor-conditions.md)
