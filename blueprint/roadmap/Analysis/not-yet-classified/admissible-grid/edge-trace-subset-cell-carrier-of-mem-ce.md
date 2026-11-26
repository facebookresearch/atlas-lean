# Edge Trace subset cell carrier of mem cell Edges

Each canonical edge of a cell lies in that cell's closed carrier.

```lean
theorem edgeTrace_subset_cell_carrier_of_mem_cellEdges
    (D : GridFilling) (v : GridIndex) {e : GridEdge} (he : e ∈ cellEdges v) :
    D.edgeTrace e ⊆ (D.cell v).carrier
```
