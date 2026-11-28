# Coverage bin packing on a topologically ordered splicing graph

Let $G = (V, E)$ be a splicing graph: a finite directed acyclic graph with an added source $s$ and sink $t$, such that every vertex lies on some $s$–$t$ path, and with an edge weight $w(e) > 0$ equal to the number of reads spanning junction $e$. Fix a topological order $v_1 = s, v_2, \dots, v_{|V|} = t$. Two edges are **compatible** if some directed path contains both, and **incompatible** otherwise.

**Cut sets are maximal incompatible sets.** For $1 \le i < |V|$ let $I_i = \{(v_a, v_b) \in E : a \le i < b\}$ be the edges crossing the gap between positions $i$ and $i + 1$. Then the edges of $I_i$ are pairwise incompatible, and every edge $e \notin I_i$ is compatible with some edge of $I_i$; so $I_i$ is a maximal set of pairwise incompatible edges.

**Packing step.** Treat each edge as a bin of capacity $c = w(e)$ and each current transcript fragment as an item of size equal to the depth it carries. When moving from one cut to the next across a vertex with $m$ incoming edges (capacities $c_1, \dots, c_m$) and $n \ge m$ items $w_1, \dots, w_n$ on its outgoing edges, items are assigned to incoming edges by the 0–1 quadratic program

$$\min_{x} \sum_{i=1}^{m} \Bigl(c_i - \sum_{j=1}^{n} w_j x_{ij}\Bigr)^2 \quad \text{s.t.} \quad \sum_{i=1}^{m} x_{ij} = 1 \ \forall j, \qquad \sum_{j=1}^{n} x_{ij} \ge 1 \ \forall i, \qquad x_{ij} \in \{0, 1\}.$$

Each item goes to exactly one bin and every bin gets at least one item, so every junction is explained by at least one transcript; unlike classical bin packing, a bin may be over- or under-filled and the objective penalizes the squared mismatch. When $m > n$ (a "trap" vertex) the roles of items and bins are swapped, with the constraint that every previously filled bin keeps at least as many items as before. Linking each assigned item to its bin extends the fragments by one vertex; sweeping cut by cut, alternating direction at trap vertices, produces a set of $s$–$t$ paths covering all edges.

**Linearization.** Each product $x_{ij} x_{ik}$ in the expanded objective is replaced by a binary $y_{ijk}$ with $y_{ijk} \le x_{ij}$, $y_{ijk} \le x_{ik}$, $x_{ij} + x_{ik} - 1 \le y_{ijk}$, which makes the program an equivalent 0–1 integer linear program.

## Expansion

Pairwise incompatibility: a directed path visits vertices in increasing topological position, so it crosses the gap between positions $i$ and $i + 1$ at most once and contains at most one edge of $I_i$. Maximality: if $e = (v_a, v_b) \notin I_i$ then either $b \le i$ or $a > i$. In the first case $v_b$ lies on a path to $t$, which must cross the gap by some edge $f \in I_i$, and $e$ followed by that path contains both $e$ and $f$; the case $a > i$ is symmetric using a path from $s$ to $v_a$. For binary variables the three linear constraints force $y_{ijk} = x_{ij} x_{ik}$, so the objective value is unchanged at every feasible point. Before packing, a vertex whose out-weight exceeds its in-weight by a user-set ratio receives an extra edge from $s$ (and symmetrically to $t$), so isoform starts and ends inside the graph are represented.

## Sources

- J. Liu, G. Li, Z. Chang, T. Yu, B. Liu, R. McMullen, P. Chen, X. Huang, "BinPacker: packing-based de novo transcriptome assembly from RNA-seq data", PLoS Computational Biology 12 (2016) e1004772, Methods, Sections 2 ("Topological ordering of splicing graph and detecting a maximal set of pairwise incompatible edges") and 3 (Steps 1–4, Equations (1) and (2)), <https://doi.org/10.1371/journal.pcbi.1004772> (PMC4760927).
