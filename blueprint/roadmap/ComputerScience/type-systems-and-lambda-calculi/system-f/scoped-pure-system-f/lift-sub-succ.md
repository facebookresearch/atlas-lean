# Lifted type substitution weakens old images

For every type substitution $\sigma$ from $n$ to $k$ type variables and every $i < n$, the [lifted substitution](lift-sub.md) satisfies $\sigma^{\uparrow}(i + 1) = \sigma(i)\langle j \mapsto j + 1\rangle$: the image of an old variable is [renamed](rename.md) by the successor.
