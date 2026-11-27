# Entries of a 4 × 4 arrowhead matrix

Ten real numbers `a`, `b₁, b₂, b₃`, `c₁, c₂, c₃` and `k₁, k₂, k₃`, read as the entries of the
[arrowhead matrix](mat.md) `[[a, b₁, b₂, b₃], [c₁, -k₁, 0, 0], [c₂, 0, -k₂, 0], [c₃, 0, 0, -k₃]]`.
No sign condition is imposed on them. The Hodgkin–Huxley [Jacobian](../hodgkin-huxley-model/jac.md)
has this shape: in its last three rows only the first and the diagonal entries can be nonzero. The
[arrowhead entries at V](arrow-at.md) are such entries, built from the steady-state gating values at
`V`.
