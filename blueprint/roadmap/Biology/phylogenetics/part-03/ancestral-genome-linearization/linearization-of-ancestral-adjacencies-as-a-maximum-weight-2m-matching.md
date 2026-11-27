# Linearization of ancestral adjacencies as a maximum weight 2m-matching

**Setting.** Ancestral genome reconstruction proposes weighted ancestral adjacencies: pairs of genes
(or gene extremities) believed to be neighbors in the ancestral genome. Encode them as a binary
matrix $M$ with one column per gene and one row per adjacency (each row of **degree** 2, that is,
with two 1 entries), and give each column $c$ a maximum copy number $m(c) \in \mathbb{N}$. Equivalently,
let $G_M$ be the simple graph whose vertices are the columns and whose weighted edges are the rows.

A degree-2 matrix (or its graph) is **component-mCi1P for $m$** if there is a collection of cyclic
walks (candidate circular chromosomes) such that (i) every edge of $G_M$ lies on one of the walks and
(ii) every vertex $v$ occurs at most $m(v)$ times in total over all walks. Linear chromosomes are
allowed as a special case. The **linearization problem** MAX-ROW-component-mCi1P asks for a subset of
rows of maximum total weight whose submatrix is component-mCi1P.

A **2m-matching** of $G$ is a spanning subgraph in which every vertex $v$ has degree at most $2m(v)$.

**Lemma.** A spanning subgraph of $G$ is component-mCi1P for $m$ if and only if it is a 2m-matching.

**Theorem.** For degree-2 matrices with weighted rows and column multiplicities, optimal
linearizations are exactly maximum weight 2m-matchings of $G_M$, and they can be computed in polynomial
time by reduction to maximum weight matching: replace each vertex $x$ by $f(x)$ copies and each edge
$e = \{x, y\}$ by a path $x_i - e_x - e_y - y_j$ through two new vertices, all edges carrying weight
$w(e)$; then $G$ has an $f$-matching of weight $w$ if and only if the new graph has a matching of weight
$w + \sum_{e} w(e)$.

In contrast, requiring a single circular chromosome (MAX-ROW-Ci1P) or only linear chromosomes
without multiplicities (MAX-ROW-C1P) is NP-complete already for degree-2 matrices, since these contain
the traveling salesman and vertex-disjoint path cover problems.

## Proof depends on

- [General matching is in P (Edmonds' blossom algorithm)](../../../../TheoryOfComputation/polynomial-time-problems/matching-in-general-graphs/matching-in-p.md)
- [Euler circuits in connected even graphs](../../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/exists-is-eulerian.md)
- [TRAVELING SALESPERSON (SYMMETRIC) is NP-complete](../../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/traveling-salesperson-problem/tsp-np-complete.md)

## Expansion

Each occurrence of a vertex on a cyclic walk contributes two incident walk edges, so a feasible
subgraph has degree at most $2m(v)$ at $v$. Conversely, given a 2m-matching, attach a new vertex $v_0$
joined to each deficient $v$ by $2m(v) - \deg(v)$ parallel edges; every degree is now even, so each
component has an Eulerian circuit, and deleting the occurrences of $v_0$ leaves cyclic walks that use
each $v$ at most $m(v)$ times. Allowing several chromosomes and repeated genes is exactly what turns a
hard Hamiltonian-type problem into a degree-bounded subgraph problem.

## Sources

- J. Maňuch, M. Patterson, R. Wittler, C. Chauve, E. Tannier, "Linearization of ancestral
  multichromosomal genomes", BMC Bioinformatics 13(Suppl 19) (2012) S11, Lemma 1 and Property 1
  (degree-2 case), <https://doi.org/10.1186/1471-2105-13-s19-s11> (PMC3526452).
