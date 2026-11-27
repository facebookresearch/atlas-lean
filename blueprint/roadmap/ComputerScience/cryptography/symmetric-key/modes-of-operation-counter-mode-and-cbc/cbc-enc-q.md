# CBC encryption as an oracle computation

Let $X$ be an additive commutative group. For a message $m \in X^\ell$ and an initial vector $\mathrm{iv}$, the oracle computation runs the [oracle form of the CBC chain](chain-q.md) from $\mathrm{iv}$ on $m$, obtaining $c \in X^\ell$, and returns $(\mathrm{iv}, c)$. It does not sample $\mathrm{iv}$, and it assumes nothing about the oracle; being a permutation is a property of the instantiation.
