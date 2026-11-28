# Complexity of binet compatibility and maximum binet compatibility

Use the definitions of binets, subnets and compatibility from [Compatibility of level-1 binets](compatibility-of-level-1-binets.md). For a digraph $G$ on $X$ let $\mathcal R(G) = \{R(x;y) : (x,y) \in E(G)\}$ be the set of reticulate binary level-1 binets it induces. The **maximum binet compatibility** problem (MBC) asks, for a set $\mathcal B$ of binary level-1 binets and an integer $k$, whether some binary network displays at least $k$ binets of $\mathcal B$, that is, whether $\mathcal B$ has a compatible subset of size at least $k$ (compatibility meaning display by a binary network; display by an arbitrary network is a different notion).

**Theorem.**
1. (Acyclicity) $\mathcal R(G)$ is compatible if and only if $G$ is acyclic.
2. (General binets) Deciding whether a thin set of arbitrary binets (not necessarily binary or level-1) is displayed by some phylogenetic network is GI-hard.
3. (MBC is hard) MBC is NP-complete.
4. (Approximation) For every set $\mathcal B$ of binary level-1 binets there is a binary level-1 network $N$ with $|\mathcal B(N) \cap \mathcal B| \ge |\mathcal B|/3$, giving a polynomial-time $1/3$-approximation for the optimization version of MBC.

## Depends on

- [Compatibility of level-1 binets](compatibility-of-level-1-binets.md)

## Expansion

Part 1: if $G$ is acyclic, order its vertices topologically as $x_1, \dots, x_n$ (arcs go from lower to higher index); a single level-1 network built along this order displays every $R(x_i;x_j)$ with $i<j$, hence all of $\mathcal R(G)$. Conversely, the asymmetric binets $R(x;y)$ induce an order relation on the leaves of any network displaying them, so a directed cycle of arcs cannot be realized. Part 2 reduces DAG isomorphism, which is GI-complete: two DAGs are encoded as binets on $\{x,y\}$ and $\{x,z\}$ by attaching a root gadget and an extra leaf, and with the third binet $T(y,z)$ the three are simultaneously displayable exactly when the DAGs are isomorphic. Part 3 reduces feedback arc set in tournaments: by part 1, a subset of $\mathcal R(G)$ of size at least $|\mathcal R(G)| - k'$ is compatible iff deleting the complementary at most $k'$ arcs makes the tournament $G$ acyclic. Part 4: if at least a third of the binets are tree type, any binary tree on $X$ displays them; otherwise fix an order $x_1, \dots, x_n$ and split the reticulate binets into those of the form $R(x_i;x_j)$ with $i<j$ and those with $i>j$; the larger class has at least $|\mathcal B|/3$ members and is displayed by one level-1 network realizing the order.

## Sources

- L. van Iersel, V. Moulton, E. de Swart, T. Wu, "Binets: fundamental building blocks for phylogenetic networks", Bulletin of Mathematical Biology 79(5) (2017) 1135–1154, Proposition 1 and Theorems 5–7, <https://doi.org/10.1007/s11538-017-0275-4>, PMCID PMC5488434.
