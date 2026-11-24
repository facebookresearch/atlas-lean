# Projected Gradient Descent Step sq norm le

Projected one-step bound, set-scoped: if `c ∈ K` and `xn` is no farther
than the unprojected update `x - η • g` from every point of `K`, then its
squared distance to `c` is bounded by the one-step expansion.

The comparator set cannot be dropped: an ambient `∀ d` hypothesis would force
`xn = x - η • g` (take `d := x - η • g`), collapsing the projection to the
identity.
