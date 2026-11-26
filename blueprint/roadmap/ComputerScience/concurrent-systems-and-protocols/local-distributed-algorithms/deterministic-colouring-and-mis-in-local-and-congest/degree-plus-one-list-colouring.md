# Degree-plus-one list colouring instance

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. A $(\deg + 1)$-list colouring instance assigns to every vertex $v$ a list $L(v)$ of colours from a colour space of size $\mathrm{poly}(n)$ with $\lvert L(v) \rvert \ge \deg(v) + 1$. A solution is a proper colouring $c$ with $c(v) \in L(v)$ for all $v$. Every such instance is solvable greedily, and $(\Delta + 1)$-colouring is the special case $L(v) = \{1, \dots, \Delta+1\}$. A partial colouring is proper on its coloured vertices; removing coloured vertices and the colours of coloured neighbours from the lists keeps the remaining instance a $(\deg + 1)$-list colouring instance.

## Depends on

- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Sources

- M. Ghaffari, F. Kuhn, "Deterministic Distributed Vertex Coloring: Simpler, Faster, and without Network Decomposition", FOCS 2021, arXiv:2011.04511.
