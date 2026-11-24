# Constraint matrix on generation and angles

For the data of a dispatch problem (buses, branches with susceptances `b`, generators at buses,
reference bus `r`), the constraint matrix on the free variables `(p, θ)` stacks, in this order, the
rows of

- `-C p + L_b θ ≤ -d` and `C p - L_b θ ≤ d`;
- `θ_r ≤ 0` and `-θ_r ≤ 0`;
- `p ≤ p_max` and `-p ≤ -p_min`;
- `f ≤ f_max` and `-f ≤ -f_min`, with `f = diag(b) Bᵀ θ`,

where `C` is the [generator incidence](generator-incidence.md) and `L_b` the
[weighted Laplacian](../dc-power-flow/weighted-laplacian.md) `L_b = B diag(b) Bᵀ`: each equation
becomes two opposite inequalities and each two-sided bound two inequalities.
