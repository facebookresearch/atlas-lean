# The least fixed point is a fixed point

Let $L$ be a complete lattice and $f : L \to L$ a monotone map, and let $\mathrm{lfp}(f) = \bigsqcap \{a \in L \mid f(a) \sqsubseteq a\}$. Then $f(\mathrm{lfp}(f)) = \mathrm{lfp}(f)$.

## Sources

- Mathlib, `OrderHom.map_lfp` in `Mathlib/Order/FixedPoints.lean`.
