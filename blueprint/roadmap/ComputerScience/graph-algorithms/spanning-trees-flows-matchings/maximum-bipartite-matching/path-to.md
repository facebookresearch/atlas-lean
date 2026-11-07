# Walking the layers back

Given the adjacency lists $\mathrm{adj}$ of a bipartite graph, a
partner assignment $\mathrm{mate}$, a level $k$ and a right vertex $j$, the walk back from $j$ at
level $k$ is a list of pairs defined by recursion on $k$. At level $0$ it is $[(i, j)]$ for the
least unmatched left vertex $i$ with $j \in \mathrm{adj}(i)$ and $\mathrm{mate}(j) \ne i$, and
empty if there is none. At level $k + 1$, if $j$ is reached within $k + 1$ rounds of the
alternating layered search, it is the walk back from $j$ at level $k$. Otherwise take the least
left vertex $i$ reached within $k + 1$ rounds with $j \in \mathrm{adj}(i)$ and
$\mathrm{mate}(j) \ne i$ (the walk is empty if there is none): if no right vertex has partner $i$
the walk is $[(i, j)]$, and otherwise it is $(i, j)$ followed by the walk back at level $k$ from
the least right vertex $j'$ with $\mathrm{mate}(j') = i$.

When $j$ is reached within $k + 1$ rounds, the walk descends to the round where $j$ is first
reached and lists the pairs to match, $j$ first.
