# Sturm chain

The Sturm chain of a real polynomial $p$ is the list $p_0, p_1, \dots, p_m$
with $p_0 = p$, $p_1 = p'$ and $p_{k+1} = -(p_{k-1} \bmod p_k)$, the negated remainder of
$p_{k-1}$ on division by $p_k$, where the list stops at $p_m$ as soon as the next entry would
be $0$; thus $p_m$ is its last entry and, for $p \ne 0$, every entry is nonzero. For $p = 0$
the chain is the one-entry list $(0)$.
