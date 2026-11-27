# Integer linear program for the gene duplication problem

**Cluster encoding of species trees.** For a finite taxon set $X$ with $|X| = n$, a family $H$ of non-empty subsets of $X$ is a **binary hierarchy** if (i) $X \in H$ and $\{x\} \in H$ for every $x \in X$, (ii) any $A, B \in H$ are compatible, $A \cap B \in \{A, B, \emptyset\}$, and (iii) $|H| = 2n - 1$. A set $H$ is the cluster set of a rooted binary tree on $X$ if and only if $H$ is a binary hierarchy. Encode a candidate species tree by a 0/1 matrix $M$ with a row per taxon and $2n-1$ columns, column $p$ representing the cluster $\{a : M(a,p) = 1\}$, with linear constraints forcing the trivial clusters, pairwise compatibility and distinct columns.

**Triple and duplication variables.** For every three taxa $\{a,b,c\}$ occurring together in some gene tree, binary variables $T(a,b,c,xyz)$ with $xyz \in \{011, 101, 110\}$ indicate that the encoded tree displays $bc|a$, $ac|b$, $ab|c$ respectively, enforced for every column $p$ by

$$T(a,b,c,011) \ge -M(a,p) + M(b,p) + M(c,p) - 1,$$

the two analogous inequalities, and $T(a,b,c,011) + T(a,b,c,101) + T(a,b,c,110) = 1$. For each internal gene-tree node $g$, a binary $D(g)$ satisfies $D(g) \ge 1 - T(a,b,c,xyz)$ for each triple of $\mathrm{Trip}_G(g)$.

**Theorem (formulation).** Minimizing $\sum_g D(g)$ subject to these constraints returns $\mathrm{Tin}(\mathcal G) = \mathrm{Dup}(\mathcal G)$, and the optimal $M$ encodes an optimal species tree. With $k$ gene trees, $n$ taxa and $m$ distinct triples, the program has $O(m)$ triple variables with $O(nm)$ constraints and $O(kn)$ duplication variables; since for $u$ with children $v,w$ and fixed $a \in L(G(u))$, $b \in L(G(v))$ a triple $xy|z$ lies in $\mathrm{Trip}_G(u)$ iff $ax|b$, $ay|b$ and $bz|a$ do, $O(n)$ triples per node suffice, giving $O(kn^2)$ duplication constraints.

## Depends on

- [Gene duplications as rooted-triple inconsistencies](gene-duplications-as-rooted-triple-inconsistencies.md)

## Expansion

A triple $ab|c$ is displayed exactly when some cluster contains $a, b$ but not $c$; each column inequality forces the corresponding $T$ to 1 when column $p$ is such a cluster, and the equality picks exactly one resolution. A node is counted ($D(g) = 1$) as soon as one of its triples is unresolved the gene-tree way, which by the equivalence theorem is exactly when $g$ is a duplication. The GD problem is NP-hard, so the ILP gives exact optima only on moderate instances (reported up to 14 taxa with 1,000 gene trees).

## Sources

- W.-C. Chang, G. J. Burleigh, D. F. Fernández-Baca, O. Eulenstein, "An ILP solution for the gene duplication problem", BMC Bioinformatics 12 (Suppl 1): S14 (2011), Definitions 7–8, Theorem 2 and the ILP formulation section, <https://doi.org/10.1186/1471-2105-12-s1-s14>, PMCID PMC3044268.
