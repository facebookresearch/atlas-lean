# Adding a completed capability at nil preserves typing

Let $n$ be a natural number, $\Delta$ an ownership context, $e$ an endpoint whose name is scoped at
depth $n$ and $c$ a capability whose protocol has head $\mathrm{end}$. If $\Delta \vdash_n
\mathbf{0}$, then $\Delta[e \mapsto c] \vdash_n \mathbf{0}$.
