# Directed expander hierarchies of logarithmic height exist and can be constructed in n^{2+o(1)} time

1. (Existence.) For every directed graph $G$ with $n$ vertices and $m$ edges and every $\phi\le 1/\mathrm{polylog}(n)$, there is a $\phi$-expander hierarchy $(D,X_1,\dots,X_\eta)$ with $|X_i|=\tilde O(m\phi^{i-1})$ for all $i$; consequently $\eta=O(\log_{1/\phi}m)=O(\log n)$.
2. (Construction.) There is a randomized algorithm that, given an $n$-vertex capacitated simple directed graph, constructs with high probability a $1/n^{o(1)}$-expander hierarchy of height $\eta=O(\log n)$ in $n^{2+o(1)}$ time.

## Proof sketch

Existence iterates directed expander decomposition: decompose $G$ into $\phi$-expanders with backward-edge set $B_2$ of size $\tilde O(\phi m)$, let $X_1$ be the edges inside the components and $D$ the forward inter-component edges, and then decompose again with respect to the terminal set $B_2$, obtaining $X_3$ of size $\tilde O(\phi|X_2|)$, and so on; each level shrinks the terminal set by a factor $\tilde O(\phi)$. The construction proceeds bottom up: having a hierarchy for $G\setminus X_i$, it uses weighted push-relabel guided by that hierarchy to find sparse level cuts or certify expansion with respect to the current terminals, with robustness of the hierarchy under flow augmentation controlling the cost.

## Depends on

- [Directed phi-expander hierarchies of a directed graph](directed-phi-expander-hierarchy.md)

## Proof depends on

- [Every directed graph has a phi-expander decomposition whose backward edges number O(phi m log m)](directed-expander-decomposition-existence.md)

## Sources

- Aaron Bernstein, Joakim Blikstad, Thatchaphol Saranurak, Ta-Wei Tu, "Maximum Flow by Augmenting Paths in n^(2+o(1)) Time", FOCS (2024), arXiv:2406.03648.
