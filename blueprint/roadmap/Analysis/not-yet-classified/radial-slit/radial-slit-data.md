# Finite radial-slit data in the unit disk

For `n : ℕ`, a `RadialSlitData n` consists
of real endpoint functions `inner,outer : Fin n→ℝ` and bounds `0≤inner(i)≤outer(i)≤1` for
each index. Intervals may overlap or have length zero. For `n=0`, the family and its union
are empty.
