# Reconstructed depth

For a cell of depth `h` on bed elevation `z` and a face of bed elevation `zF` (real numbers,
elevations measured upward from a fixed datum), the reconstructed depth is
`h′ = max(0, h + z - zF)`: the height of the cell's free surface above the face bed, truncated at
zero (source (2.13) of Audusse et al.). The scheme takes the face bed `zF = max(zL, zR)` of the two
cells (source (2.9)).
