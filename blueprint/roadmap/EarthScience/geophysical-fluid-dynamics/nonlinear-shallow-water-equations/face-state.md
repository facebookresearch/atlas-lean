# Reconstructed face state

For a cell of depth `h`, velocity `u` and bed elevation `z` and a face of bed elevation `zF`, the
reconstructed face state is the conserved pair `(h′, h′ u)` (mass, momentum), with the
[reconstructed depth](face-depth.md) `h′ = max(0, h + z - zF)`: the cell velocity `u` is carried
unchanged (source (2.12)).
