# Greedy Inv

The greedy invariant for the list $xs$ of variables still to assign and a partial assignment $\sigma$: every variable $y$ not in $xs$ has $\sigma(y)$ in its domain, and if $y$ has a parent $p$, then $p$ is not in $xs$ (it is assigned) and $\sigma(p)$, $\sigma(y)$ are compatible on the arc from $p$ to $y$. A root has no parent condition: an assigned root with a value in its domain satisfies the invariant.
