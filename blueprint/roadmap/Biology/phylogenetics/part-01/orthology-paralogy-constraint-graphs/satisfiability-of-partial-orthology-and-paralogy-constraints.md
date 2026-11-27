# Satisfiability of partial orthology and paralogy constraints

**Setting.** Let $\mathcal{G}$ be a gene family, each gene $x$ in a species $s(x)$. A **DS-tree** is a
rooted tree with leaf set $\mathcal{G}$ whose internal nodes are labeled $\mathrm{Dup}$ (duplication) or
$\mathrm{Spec}$ (speciation). Two genes are **orthologous** with respect to a DS-tree $G$ if their lowest
common ancestor $\mathrm{lca}_G(x, y)$ is a speciation node and **paralogous** if it is a duplication node.

A **constraint graph** $R = (V, E, U)$ has vertex set $V = \mathcal{G}$, orthology edges $E$, unknown
edges $U$, and paralogy non-edges (all pairs in neither set); genes of the same species are always
paralogy non-edges. A DS-tree **satisfies** $R$ if every pair in $E$ is orthologous and every
paralogy non-edge is paralogous; pairs in $U$ are unconstrained. $R$ is **full** if $U = \emptyset$.
For $F \subseteq U$ the **realization** $R(F) = (V, E \cup F, \emptyset)$ declares $F$ orthologous and
$U \setminus F$ paralogous; $R(\emptyset)$ and $R(U)$ are the empty and full realizations, and
$\overline{R(U)}$ is the complement graph of $R(U)$.

**Theorem (full constraints).** A full constraint graph is satisfiable if and only if it is
$P_4$-free (a cograph), that is, no four vertices induce a path on four vertices. Equivalently, for
every vertex subset $X$ with $|X| \ge 2$, the induced graph or its complement is disconnected.

**Heredity.** $R$ is satisfiable if and only if $R[X]$ is satisfiable for every $X \subseteq V$.

**Theorem (partial constraints).** Let $R = (V, E, U)$ with $|V| \ge 2$. Then $R$ is satisfiable if and only if at least one holds:

1. $R(\emptyset)$ is disconnected and all its connected components are satisfiable;
2. $\overline{R(U)}$ is disconnected and all its connected components are satisfiable.

**Algorithm.** Recursively split on the components of $R(\emptyset)$ (creating a $\mathrm{Dup}$ node) or,
failing that, of $\overline{R(U)}$ (creating a $\mathrm{Spec}$ node), stopping at single genes (a one-gene
graph is satisfied by the one-leaf DS-tree) and reporting unsatisfiability when a part with at least two
genes has both graphs connected. This builds a satisfying DS-tree or certifies none exists in $O(n^3)$ time for
$n = |\mathcal{G}|$.

## Expansion

Every pair split by a duplication root is paralogous and every pair split by a speciation root is
orthologous, so the root of a satisfying tree must separate components of the "orthology" graph
(all such pairs are paralogy non-edges) or of its complement. Choosing all unknowns paralogous makes
the orthology graph as disconnected as possible, and choosing them all orthologous does the same for
its complement, so these two extreme realizations are the only ones to test at each level. If both
are connected, every realization $R(F)$ and its complement are connected, so $R(F)$ contains an
induced $P_4$ and the full-constraint theorem rules it out. The problem is an instance of the cograph
sandwich problem.

## Sources

- M. Lafond, N. El-Mabrouk, "Orthology and paralogy constraints: satisfiability and consistency",
  BMC Genomics 15(Suppl 6) (2014) S12, Definitions 2-3, Theorem 2, Lemmas 1 and 3, Theorem 3 and
  algorithm BuildDSTree, <https://doi.org/10.1186/1471-2164-15-s6-s12> (PMC4240720).
