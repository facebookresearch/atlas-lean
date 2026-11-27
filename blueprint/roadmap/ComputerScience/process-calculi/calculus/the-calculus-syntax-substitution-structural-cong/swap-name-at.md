# Swapping adjacent de Bruijn indices in a name

For a cutoff $k \in \mathbb{N}$, swapping the indices $k$ and $k + 1$ in a [channel name](name.md) sends $\#k$ to $\#(k + 1)$, $\#(k + 1)$ to $\#k$, and leaves every other variable and every free channel unchanged: the two binders at that depth exchange places.
