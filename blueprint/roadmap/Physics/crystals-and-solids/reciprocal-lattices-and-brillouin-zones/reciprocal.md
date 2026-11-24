# Reciprocal lattice in the 2π convention

Let `Λ` be a [Bravais lattice](../bravais-lattices/bravais-lattice.md) with basis matrix `B`, whose
columns are the primitive vectors `a₁`, `a₂`, `a₃` (so `det B ≠ 0`), and let `V = det B`. The
reciprocal lattice of `Λ` is the Bravais lattice with basis matrix `(2π / V) C`, where `C` is the
[cross-column matrix](cross-columns.md) of `B`; its primitive vectors are

`b₁ = (2π / V) (a₂ × a₃)`, `b₂ = (2π / V) (a₃ × a₁)`, `b₃ = (2π / V) (a₁ × a₂)`.

This is the physics convention `aᵢ · bⱼ = 2π δᵢⱼ` ([duality](inner-primitive-vector-reciprocal.md)),
not the crystallographic convention without the factor `2π`. Since `V ≠ 0`, the basis matrix of the
reciprocal lattice is nonsingular.
