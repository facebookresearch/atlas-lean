# Execution in the LOCAL model

Let $A$ be an [algorithm in the LOCAL model](local-algorithm.md), $G$ a simple graph on a finite set $V$ of nodes, $\mathrm{id} : V \to \mathbb{N}$ a map giving each node an identifier, not necessarily injective, and $x : V \to I$ a map giving each node an input. The state $s_k(v)$ of the node $v$ after $k$ synchronous rounds of $A$ on $G$ is defined by recursion on $k$: $s_0(v) = \mathrm{init}(\mathrm{id}(v), x(v))$, and $s_{k+1}(v) = \mathrm{update}(s_k(v), m)$, where $m$ is the multiset of the messages $\mathrm{send}(s_k(u), \mathrm{id}(v))$ over the neighbours $u$ of $v$ in $G$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992: §1.
