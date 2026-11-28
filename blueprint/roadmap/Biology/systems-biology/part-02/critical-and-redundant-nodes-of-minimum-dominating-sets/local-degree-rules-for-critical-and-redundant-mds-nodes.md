# Local degree rules for critical and redundant MDS nodes

**Setting.** Let $G = (V, E)$ be a finite simple undirected graph, for example a protein interaction network. A set $M \subseteq V$ is *dominating* if every node is in $M$ or adjacent to a node of $M$; a *minimum dominating set* (MDS) is a dominating set whose size is the domination number of $G$. Over the family of all MDSs of $G$, a node $v$ is

- *critical* if $v$ belongs to every MDS,
- *redundant* if $v$ belongs to no MDS,
- *intermittent* otherwise.

**Proposition A (two leaves force a critical node).** If a node $v$ has two or more neighbours of degree $1$, then $v$ is critical.

**Proposition B (a node surrounded by critical nodes is redundant).** If a node $v$ has at least one neighbour and every neighbour of $v$ is critical, then $v$ is redundant.

**Pre-processing scheme.** Apply Proposition A to every node, then Proposition B to every remaining node. The nodes so labeled are fixed in (critical) or out of (redundant) the integer linear program for the MDS, and only the remaining nodes need the exact per-node test: solve the MDS ILP once, then for each MDS node not yet labeled decide criticality, and for each non-MDS node not yet labeled decide redundancy, each by a further ILP with the node forced out or in. In scale-free graphs, where many nodes have degree $1$ and hubs tend to be critical, this removes most ILP solves and constraints.

## Depends on

- [Dominating set](../../../../GraphTheory/independence-and-domination/dominating-sets/is-dominating.md)
- [Domination number](../../../../GraphTheory/independence-and-domination/dominating-sets/domination-number.md)

## Expansion

Proposition A: let $u_1, u_2$ be leaves attached to $v$ and suppose an MDS $M$ omits $v$. The only node that can dominate $u_r$ other than $u_r$ itself is $v$, so $u_1, u_2 \in M$. Then $M' = (M \setminus \{u_1, u_2\}) \cup \{v\}$ still dominates: $v$ dominates itself, $u_1$, $u_2$, and every node formerly dominated by $u_1$ or $u_2$ is one of $u_1$, $u_2$, $v$. But $|M'| = |M| - 1$, contradicting minimality.

Proposition B: suppose an MDS $M$ contains $v$. All neighbours of $v$ are critical, hence in $M$. Removing $v$ keeps domination: $v$ is dominated by any of its neighbours, and every other node that $v$ dominated is a neighbour of $v$ and therefore lies in $M$. So $M \setminus \{v\}$ is a smaller dominating set, a contradiction. (The hypothesis that $v$ has a neighbour is needed: an isolated node is in every dominating set.)

Both rules use only the neighbourhood of a node, so they cost $O(|V| + |E|)$ in total. On synthetic scale-free networks with degree exponent $\gamma = 2$ and mean degree $2$ the resulting exact procedure ran about 180 times faster than the previous all-ILP method and handled up to $10{,}000$ nodes; with $\gamma = 2.5$ and mean degree $3$ it reached $25{,}000$ nodes. Applied to protein interaction networks of eight organisms, the critical set is small (under about $10\%$ of proteins), enriched in high-degree proteins and significantly enriched in essential genes (two-sided Fisher exact test, $P<0.05$ in all organisms except fission yeast).

## Sources

- M. Ishitsuka, T. Akutsu, J. C. Nacher, "Critical controllability in proteome-wide protein interaction network integrating transcriptome", Scientific Reports 6 (2016) 23541, Methods: Proposition 2.2 (critical proposition, quoted from earlier work of Nacher and Akutsu), Proposition 1 (redundant proposition) and the algorithm description; Results: Figure 2 and Table 1, <https://doi.org/10.1038/srep23541>, PMCID PMC4819195.
