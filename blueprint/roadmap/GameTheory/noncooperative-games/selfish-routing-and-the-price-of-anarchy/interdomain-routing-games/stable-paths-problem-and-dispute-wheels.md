# Stable paths problem and dispute wheels

A *stable paths problem* consists of a finite graph with a destination $d$, for each node $u \ne d$ a set of permitted simple paths from $u$ to $d$, and a ranking of these paths (with the empty path ranked lowest and paths with different next hops strictly ordered). A path assignment $\pi$ is *stable* if $\pi(d) = (d)$ and every node chooses its highest-ranked permitted path of the form $u$ followed by a neighbour's chosen path (or none if no such path exists). A *dispute wheel* is a cyclic sequence of nodes $u_0, \dots, u_{k-1}$ with spoke paths $Q_i$ from $u_i$ to $d$ and rim paths $R_i$ from $u_i$ to $u_{i+1}$ such that each $R_i Q_{i+1}$ is permitted and preferred by $u_i$ to $Q_i$.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)

## Sources

- Timothy G. Griffin, F. Bruce Shepherd and Gordon Wilfong, "The Stable Paths Problem and Interdomain Routing", IEEE/ACM Transactions on Networking, 2002.
- Joan Feigenbaum, Michael Schapira and Scott Shenker, "Distributed Algorithmic Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
