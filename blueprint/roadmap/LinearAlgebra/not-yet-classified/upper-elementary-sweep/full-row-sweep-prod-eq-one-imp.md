# Full Row Sweep Prod eq one imp

Coefficient uniqueness for ordered full row-sweep products.

If the ascending ordered product of all row sweeps `rowSweep r (v r)` over
`r : Fin n` equals one, then every sweep coefficient `v r i` equals one.
The proof reads matrix entries in descending row order: every ordered prefix
product is upper-triangular with diagonal one, and the column of the next
index is untouched by earlier factors, so the vanishing of the full product
forces each coefficient to vanish in turn, starting from the last row. The
argument is uniform in `n`, including the degenerate ranks `0` and `1`.

This proves only the product-equal-one implication. It makes no claim about
injectivity of equality between two ordered products, ordered normal forms,
`toStableE` injectivity, TWT closure, kernel generation, or Matsumoto's
theorem.
