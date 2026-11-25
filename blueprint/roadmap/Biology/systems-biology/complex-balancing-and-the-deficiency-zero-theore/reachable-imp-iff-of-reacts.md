# A property unchanged by reactions is constant on each linkage class

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and reaction set $\rho$, and let $P$ be a property of vectors in $\mathbb{N}^S$ such
that $P(y)$ holds if and only if $P(y')$ holds whenever $y \to y'$ (the
[reaction relation](../../../Dynamics/smooth-dynamics/reacts.md)). If two
[complexes](../../../Dynamics/smooth-dynamics/complexes.md) $c$ and $c'$ of $N$ lie in the same
linkage class, that is, they are joined by a path in the
[linkage graph](../../../Dynamics/smooth-dynamics/linkage-graph.md), then $P(c)$ holds if and only
if $P(c')$ holds.

So two complexes of which exactly one satisfies $P$ lie in different linkage classes; this is the
usual way to separate linkage classes.
