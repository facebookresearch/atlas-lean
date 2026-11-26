# The least fixed point lies below every pre-fixed point

Let $L$ be a complete lattice and $f : L \to L$ a monotone map, and let $\mathrm{lfp}(f) = \bigsqcap \{a \in L \mid f(a) \sqsubseteq a\}$. If $a \in L$ satisfies $f(a) \sqsubseteq a$, then $\mathrm{lfp}(f) \sqsubseteq a$.

## Sources

- Mathlib, `OrderHom.lfp_le` in `Mathlib/Order/FixedPoints.lean`.
