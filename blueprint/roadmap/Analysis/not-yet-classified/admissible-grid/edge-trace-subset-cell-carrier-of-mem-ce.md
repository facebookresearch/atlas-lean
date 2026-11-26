# Every edge of a grid cell lies in its closed square

Let `D` be a finite grid filling
of scale `t>0`. If `e` is one of the four edges adjacent to the cell at `v∈ℤ²`, then
`D.edgeTrace(e)⊆carrier(D.cell(v))`. The cell need not be selected.
