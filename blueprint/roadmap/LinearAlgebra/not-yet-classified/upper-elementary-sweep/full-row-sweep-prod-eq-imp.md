# Full Row Sweep Prod eq imp

Coefficient uniqueness for equal ordered full row-sweep products.

If the ascending ordered products of all row sweeps `rowSweep r (v r)` and
`rowSweep r (w r)` over `r : Fin n` agree, then every sweep coefficient agrees:
`v r i = w r i`. The proof peels the two products from the last row downward:
each peeled middle difference collapses to a single sweep by the homomorphism
equations, and the column of the next index is untouched by earlier factors, so
reading its entries forces each coefficient difference to vanish in turn. The
argument is uniform in `n`, including the degenerate ranks `0` and `1`.

This proves only coefficient uniqueness for equal full ordered products. It makes
no claim about ordered normal forms, `toStableE` injectivity, TWT closure,
kernel generation, Steinberg relations, or Matsumoto's theorem.
