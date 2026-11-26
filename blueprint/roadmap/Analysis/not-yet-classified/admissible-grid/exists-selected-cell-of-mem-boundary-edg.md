# Exists selected cell of mem boundary Edges

Each reduced boundary edge lies in at least one selected cell's closed carrier.

```lean
theorem exists_selected_cell_of_mem_boundaryEdges
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    ∃ v ∈ D.cells, D.edgeTrace e ⊆ (D.cell v).carrier
```
