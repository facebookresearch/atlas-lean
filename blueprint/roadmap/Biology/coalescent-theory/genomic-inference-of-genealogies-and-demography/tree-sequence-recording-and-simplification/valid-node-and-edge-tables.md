# Valid node and edge tables define a forest at every genomic position

A **node table** is a finite list of nodes $u$, each with a birth time $\tau(u) \in \mathbb R$, measured backwards (time ago). An **edge table** is a finite list of edges $(\ell, r, p, c)$ with $0 \le \ell < r \le L$: on the half-open genomic interval $[\ell, r)$, node $c$ inherits from parent node $p$. Sites and mutations may be added: a site has a position and an ancestral state, and a mutation names a site, the first node to carry it, and a derived state.

The tables are **valid** if

1. **parents are older than children:** $\tau(p) > \tau(c)$ for every edge $(\ell, r, p, c)$, and
2. **one parent per position:** for each node $c$, the intervals $[\ell, r)$ of the edges with child $c$ are pairwise disjoint.

**Claim.** If the tables are valid, then for every position $x \in [0, L)$ the edges with $\ell \le x < r$ form the parent map of a forest: each node has at most one parent at $x$, and following parents strictly increases $\tau$, so there are no directed cycles. The forest changes only at the finitely many edge endpoints. Whether each forest is a single tree is a separate condition.

**Forward-time recording (Algorithm W).** A simulation can produce such tables by appending one row per new genome: its birth time to the node table, and one edge per parental segment it inherits to the edge table. For a haploid Wright–Fisher population with one crossover per birth at $x$, the newborn $u$ with parents $a, b$ gets the edges $(0, x, a, u)$ and $(x, L, b, u)$. New mutations go in the site and mutation tables at the node where they arise. Neutral mutations can instead be placed afterwards on the marginal trees.

## Expansion

At a fixed $x$, condition 2 leaves at most one active edge per child, so the active edges define a partial function $\pi_x$ from children to parents. Condition 1 makes $\tau$ strictly increase along $u, \pi_x(u), \pi_x^2(u), \dots$, so no node repeats and the graph is acyclic, hence a forest. The active set changes only at edge endpoints. In Algorithm W each newborn has strictly later birth time than its parents, which gives condition 1, and its two edges cover disjoint intervals, which gives condition 2. Converting the clock to time ago before analysis is a monotone relabeling that preserves both conditions.

## Sources

- J. Kelleher, K. R. Thornton, J. Ashander and P. L. Ralph, "Efficient pedigree recording for fast population genetics simulation", *PLoS Computational Biology* 14(11) (2018), e1006581, <https://doi.org/10.1371/journal.pcbi.1006581> (PMC6233923), sections "Tables for succinct tree sequences" (subsection "Validity of a set of tables"), "Recording the pedigree in forwards time" (Algorithm W) and "Essential steps in tree sequence recording".
