# Evaluation is stable under renaming

Let $\rho$ and $\rho'$ be environments and
$r : \mathbb{N} \to \mathbb{N}$ a renaming such that, for every index $i$ and value $w$, if $\rho$
has entry $w$ at index $i$ then $\rho'$ has entry $w$ at index $r(i)$. If a target term $e$
evaluates to $v$ in $\rho$, then the renaming of $e$ by $r$ evaluates to $v$ in $\rho'$.
