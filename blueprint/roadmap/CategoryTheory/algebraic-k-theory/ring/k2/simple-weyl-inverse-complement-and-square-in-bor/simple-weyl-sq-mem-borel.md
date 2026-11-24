# Simple Weyl sq mem borel

Square of the simple Weyl element lies in the finite Borel: for
`hm : m + 1 < n` and `s = weyl m (m + 1) 1`, `s * s ∈ finiteBorelSubgroup n`.
Purpose: tiny public `s² ∈ B` wrapper for Lemma-25 torus normalization.
Since `torus(-1) = s⁻¹ * s⁻¹`, `s * s = torus(-1)⁻¹` lies in the finite
torus, hence in the Borel. Characteristic-two safe.
Orientation: none beyond the product order `s * s`.
Nonclaim: no Lemma 25, Bruhat, quotient, or Matsumoto claim.
