# Global stiffness matrix of a planar frame element

For real `EA`, `EI`, `L`, `c` and `s`, the global stiffness matrix of a planar frame element is
`K_g = Tᵀ K_f T`, with the [frame transformation](frame-rotation.md) `T` and the local
[frame stiffness matrix](frame-stiffness.md) `K_f`; the local displacements are `T d` for global
displacements `d`. At `L = 0` it is the zero matrix, since `K_f` is. The physical reading is
`EA > 0`, `EI > 0`, `L > 0` and `c² + s² = 1`, with `(c, s)` the direction cosines of the element
axis; then `T` is orthogonal and `K_g` is the local stiffness expressed in global coordinates.
