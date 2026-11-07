# Assembled stiffness matrix of the P1 method

The assembled stiffness matrix `K = ∑ᵢ (1 / hᵢ) eᵢ eᵢᵀ` on all nodes:
each element contributes `(1 / hᵢ) [[1, -1], [-1, 1]]` at nodes `i, i + 1`.
