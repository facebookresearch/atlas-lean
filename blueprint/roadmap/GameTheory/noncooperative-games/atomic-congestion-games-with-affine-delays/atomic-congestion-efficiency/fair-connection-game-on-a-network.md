# Fair connection game on a network

A *fair connection game* is played on a directed multigraph or undirected graph with nonnegative edge costs $c_e$. Each of $k$ players chooses a simple path from its source $s_i$ to its sink $t_i$; the cost of each used edge is split equally among the players using it, and the social cost is the total cost of the edges in the formed subnetwork. It is a fair cost-sharing game whose resources are edges, and its optimum is a minimum-cost Steiner forest connecting all terminal pairs.

## Depends on

- [Fair cost-sharing game](../../potential-games/fair-cost-sharing.md)

## Sources

- Elliot Anshelevich et al., "The Price of Stability for Network Design with Fair Cost Allocation", SIAM Journal on Computing, 2008.
- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
