# Type erasure of System F terms to untyped terms

The type erasure of a [System F term](../scoped-pure-system-f/tm.md) $t \in \mathrm{Tm}_{n,m}$ is the untyped de Bruijn term $|t|_\iota$, its [erasure](erase-with.md) under the environment $\iota$ sending each term variable $i$ to the bound index $i$.
