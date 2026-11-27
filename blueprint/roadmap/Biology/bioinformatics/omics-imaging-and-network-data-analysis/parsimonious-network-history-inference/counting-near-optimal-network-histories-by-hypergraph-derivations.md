# Counting near-optimal network histories by hypergraph derivations

**Network history problem.** Given present-day protein interaction networks and binary gene trees whose internal nodes are duplications or speciations, an interaction event $(u, v, \pm)$ gains or loses an interaction between ancestral proteins $u, v$ (neither an ancestor of the other). Interactions are inherited through duplications. A set of events is valid if it is logically and temporally consistent, and it reconstructs the data if the inherited interactions at the leaves are exactly the observed ones. The **network history inference problem** asks for a valid reconstructing set of minimum total cost $\sum c(e)$ (Problem 1).

**Hypergraph encoding.** Build an acyclic directed ordered hypergraph whose vertices are pairs $(\{u,v\}, \text{present/absent})$, meaning the interaction state between $u$ and $v$ just before either duplicates. Hyperarcs recurse into the children of $u$ or of $v$, with cost $0$ for keeping the state and the gain or loss cost for switching it, with special arcs for homodimers $\{u,u\}$, and leaf arcs whose cost is $0$ or one event depending on whether the observed edge agrees. A **derivation** is a tree of hyperarcs from the root down to leaves; its cost is the sum of hyperarc costs, and the optimal derivation satisfies the recurrence

$$\delta(v) = \min_{e \in \mathrm{BS}(v)} \Big( c(e) + \sum_{i} \delta(t_i(e)) \Big),$$

where $\mathrm{BS}(v)$ is the backward star of $v$ and $t_i(e)$ the tail vertices.

**Theorem 2.** The gains and losses read off the state switches of an optimal derivation form a minimum-cost solution of Problem 1, except that the set may contain temporally inconsistent events.

**Counting cost classes.** Let $D_j(x)$ be the set of derivations rooted at $x$ in the $j$-th best cost class, with common cost $c_j(x)$. For a hyperarc $e$ with tail $(t_1, \dots, t_r)$ and a vector of cost classes $\mathbf d = (d_1, \dots, d_r)$,

$$\#\{\text{derivations using } e \text{ and classes } \mathbf d\} = \prod_{i=1}^r |D_{d_i}(t_i)|, \qquad |D_j(x)| = \sum_{e \in \mathrm{BS}(x)} \ \sum_{\mathbf d:\ c(e) + \sum_i c_{d_i}(t_i) = c_j(x)} \ \prod_i |D_{d_i}(t_i)| .$$

**Lemma 3.** Write a combination at $x$ as a pair $(e, \mathbf d)$ with $e \in \mathrm{BS}(x)$ and $\mathbf d$ a vector of cost classes of the tails of $e$, of cost $c(e) + \sum_i c_{d_i}(t_i)$. Lowering one index $d_i \ge 2$ of $\mathbf d$ by one gives a strictly cheaper combination, since $c_1(t) < c_2(t) < \cdots$. Hence every combination not of the form $(e, (1, \dots, 1))$ has a strictly cheaper neighbour, and a best-first priority queue seeded with $(e, (1, \dots, 1))$ for every $e \in \mathrm{BS}(x)$, which on popping $(e, \mathbf d)$ pushes the combinations obtained by raising one index of $\mathbf d$ by one, pops the combinations at $x$ in nondecreasing cost. Processing vertices in topological order, the top-$k$ cost classes and their sizes are therefore enumerated without listing individual derivations. (The source states Lemma 3 as "every class-$(j+1)$ combination arises from a class-$j$ combination by raising one index by one"; that form is false, e.g. for a vertex with two hyperarcs with empty tails and costs $0$ and $1$, and the enumeration needs only the property above.)

## Expansion

The hypergraph makes the parsimony recurrence explicit: each vertex is a subproblem, each hyperarc a way to solve it from subproblems, and acyclicity lets values be computed from the leaves upward. Because the number of derivations of a given cost depends only on the cost classes chosen for the tails, sizes multiply across tails and add across alternatives, exactly as in counting paths in a DAG. Monotonicity of costs in each tail coordinate gives the neighbor structure of Lemma 3, so best-first search pops combinations in cost order, the same idea as cube pruning for $k$-best parsing. Weighting each near-optimal history by its cost, the sizes $|D_j|$ yield an ensemble over histories in which the posterior frequency of any given interaction gain, loss, or ancestral edge is computed by summing over the counted ensemble, and is used to predict ancestral networks and missing present-day interactions.

## Sources

- R. Patro, C. Kingsford, "Predicting protein interactions via parsimonious network history inference", Bioinformatics 29(13) (2013) i237-i246, Sections 2-3, Problem 1, Equations (1)-(10), Theorem 2 and Lemma 3, <https://doi.org/10.1093/bioinformatics/btt224>, PMCID PMC3694678.
