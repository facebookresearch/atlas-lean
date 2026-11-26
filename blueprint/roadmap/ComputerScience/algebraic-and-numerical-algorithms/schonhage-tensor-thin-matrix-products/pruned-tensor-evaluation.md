# Pruned evaluation of the tensor recursion

The recursive evaluation of the $L$-fold tensor power that descends only into children with at least one requested output string, reading precomputed leaf encodings, returns on every requested output exactly the value of the full bilinear expansion and $0$ elsewhere. Its recursive calls depend only on the requested set (not on the encoded values), and their number is at most the total size of the requested sets passed down plus one.

## Depends on

- [Leaves of the tensor power and their order](tensor-power-leaves-and-order.md)

## Proof depends on

- [Schönhage's ten-term polynomial identity with error term](schonhage-ten-term-identity.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
