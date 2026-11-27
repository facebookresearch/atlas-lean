# Nonnegativity of a transfer step

On a finite directed network, let stocks $m(v) \ge 0$, sources $s(v) \ge 0$, arc rates $\alpha_e \ge 0$ with flows $F_e = \alpha_e m(\mathrm{tail}\,e)$, and removals $r(v) = \delta_v m(v)$, where at each node the outgoing rates and $\delta_v$ sum to at most $1$. Then the updated stock $m' = m + B F + s - r$, with $B$ the incidence matrix (incoming minus outgoing flow), is nonnegative at every node.
