# Restricted graphs and the parameter kappa counting negative edges on nonpositive paths

A directed graph $G=(V,E,w)$ with a designated source $s\in V$ is *restricted* if (i) all weights are integers with $w(e)\ge -1$; (ii) every directed cycle $C$ satisfies $w(C)\ge|C|$, that is, the minimum cycle mean is at least $1$ if $G$ has a cycle (the condition is vacuous for acyclic $G$); and (iii) $s$ has an edge of weight $0$ to every other vertex. A restricted graph has no negative cycle. The *Restricted SSSP* problem asks for a shortest-path tree from $s$ in a restricted graph. For a restricted graph define

$$
\kappa(G)=\max\{|\{e\in P: w(e)=-1\}| : P \text{ a simple path starting at } s \text{ with } w(P)\le 0\}.
$$

## Depends on

- [Negative-weight single-source shortest paths with integer weights bounded below by -W](negative-weight-sssp-integer-weights.md)
- [Minimum cycle mean of a weighted edge list](../minimum-cycle-mean/is-min-cycle-mean.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
