# Type substitution commutes with instantiation

For a type substitution $\sigma$ from $n$ to $k$ type variables, $B \in \mathrm{Ty}_{n+1}$ and $A \in \mathrm{Ty}_n$, $B[A][\sigma] = (B[\sigma^{\uparrow}])[A[\sigma]]$ ([instantiation](../scoped-pure-system-f/instantiate.md), [lifted substitution](../scoped-pure-system-f/lift-sub.md)).
