# Midpoint rule for the interior load on the bar

For a real `L` and a load function `q`, the midpoint load of the interior node on the two-cell mesh
of `[0, L]` is `(L/2) q(L/4) φ((L/4) / L) + (L/2) q(3L/4) φ((3L/4) / L)`, where `φ` is the
[hat function](../finite-element-method-in-one-dimension/hat.md) of the interior node of the
[two-cell partition](two-cells.md); each cell of width `L/2` contributes at its midpoint.
