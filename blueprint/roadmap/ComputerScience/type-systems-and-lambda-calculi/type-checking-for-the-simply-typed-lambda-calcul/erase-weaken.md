# Erasure of a weakened term

For every intrinsically typed term $t$ in context $\Gamma$
and every type $B$, the erasure of the weakening of $t$ to the context $\Gamma$ extended by
$B$ equals the raw renaming by the successor map $n \mapsto n + 1$ (lifted at every binder)
of the erasure of $t$. Thus every free index is incremented by one.
