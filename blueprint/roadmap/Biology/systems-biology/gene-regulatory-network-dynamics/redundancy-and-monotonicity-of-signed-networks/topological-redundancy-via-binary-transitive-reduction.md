# Topological redundancy of a signed network via binary transitive reduction

**Signed network model.** A cellular signaling, transcriptional or metabolic network is a directed graph $G = (V,E,w)$ with edge signs $w:E\to\{-1,+1\}$ (activation or inhibition). The parity of a path $P$ is $\prod_{e\in P} w(e)$. For $E'\subseteq E$, let $\mathrm{reachable}(E')$ be the set of ordered triples $(u,v,x)$ such that the subgraph $(V,E')$ contains a path from $u$ to $v$ of parity $x\in\{-1,1\}$ (the empty path gives $(u,u,1)$). An unsigned network, such as a social network, is the case $w\equiv 1$.

**Binary transitive reduction (BTR).** Given $G$ and a set $E_{\mathrm{critical}}\subseteq E$ of edges that must be kept, find $E'$ with $E_{\mathrm{critical}}\subseteq E'\subseteq E$ and $\mathrm{reachable}(E') = \mathrm{reachable}(E)$ minimizing $|E'|$. An edge is removable when an alternative pathway of the same sign connects its endpoints. With $w\equiv 1$ and $E_{\mathrm{critical}} = \emptyset$ this is the minimum equivalent digraph problem, so BTR is NP-hard.

**Redundancy measure.** With $E_{\mathrm{critical}} = \emptyset$ and $E'$ an optimal BTR solution,

$$
\mathcal{R}_{\mathrm{new}} = 1 - \frac{|E'|}{|E|}\in[0,1),
$$

larger values meaning more redundant networks. It depends on paths of arbitrary length, not only on local degree data: two graphs with identical in- and out-degree sequences can have $\mathcal{R}_{\mathrm{new}} = 0$ and $\mathcal{R}_{\mathrm{new}} = 3/11$, and the complete bipartite digraph $K_{n/2,n/2}$ (all edges directed one way) has average degree $n/2$ but $\mathcal{R}_{\mathrm{new}} = 0$.

**Computation.** Every strongly connected component is either single-parity (between any two of its vertices, paths of exactly one parity exist) or multiple-parity (both parities exist). Exploiting this, a polynomial-time algorithm with worst-case time $O(n^3)$ returns a feasible $E'$ at most $3$ times the optimum size (a $3$-approximation).

## Proof sketch

BTR preserves all pathway-level information (which node can excite or inhibit which) while deleting shortcuts that are implied by longer same-sign pathways, so $|E'|/|E|$ measures how compressible the network is. In the source the approximation is near-optimal in practice and scales to networks with thousands of nodes, and the significance of $\mathcal{R}_{\mathrm{new}}$ is assessed by a one-sample $t$-test against $100$ random networks from a null model (exponential in-degree and power-law out-degree random networks for signaling and transcriptional networks, a Markov-chain randomization for the others). Applied to real networks, the measure finds social networks more redundant than biological ones, transcriptional networks less redundant than signaling networks, and much of the redundancy of a metabolic network due to currency metabolites.

## Sources

- Réka Albert, Bhaskar DasGupta, Rashmi Hegde, Gowri Sangeetha Sivanathan, Anthony Gitter, Gamze Gürsoy, Pradyut Paul and Eduardo Sontag, "Computationally efficient measure of topological redundancy of biological and social networks", *Physical Review E* 84 (2011), 036117, <https://doi.org/10.1103/physreve.84.036117>. Preprint version: arXiv:1108.6113 (2011), Section 3 (network model), Section 4 (BTR problem, the redundancy measure, its properties and computation), <https://doi.org/10.48550/arXiv.1108.6113>.
