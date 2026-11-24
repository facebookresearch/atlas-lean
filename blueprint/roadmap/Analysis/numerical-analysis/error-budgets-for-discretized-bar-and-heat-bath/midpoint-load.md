# Composite midpoint rule for the load vector

For a [partition](../../real-functions/integration/riemann-integral/partition.md) `P` of `[0, 1]`, a
function `f` and a node `j`, the midpoint load is `∑_i h_i f(m_i) φ_j(m_i)`, summed over the cells
`i` of `P`, with the cell [width](../finite-element-method-in-one-dimension/width.md) `h_i`, the
cell midpoint `m_i` and the [hat function](../finite-element-method-in-one-dimension/hat.md) `φ_j`
of node `j`.
