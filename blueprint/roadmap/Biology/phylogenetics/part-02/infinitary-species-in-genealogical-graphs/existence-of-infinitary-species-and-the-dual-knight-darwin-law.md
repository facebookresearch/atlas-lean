# Existence of infinitary species and the dual Knight–Darwin law

Let $G = (V,E)$ be the genealogical graph of all individuals that ever live, with a directed edge from each parent to each child. Assume:

- (A1) $G$ has only finitely many roots (parentless individuals);
- (A2) no individual has infinitely many children;
- (A3) each $v \in V$ has a birthdate $t(v) \in \mathbb{R}$ with $t(u) < t(v)$ whenever $u$ is a parent of $v$, and for every $x \in \mathbb{R}$ only finitely many individuals are born before $x$;
- (A4) $G$ is infinite.

Two infinite sets are **almost equal** if their symmetric difference is finite. An **infinitary genus** is an infinite set of individuals closed under ancestry; equivalently, an infinite set that is closed in the topology on $V$ whose basic open sets are clades (an individual with all its descendants). An infinite set is almost an infinitary genus iff it is almost a birthdate genus (a set born after some time $t$ all of whose outside ancestors are born before $t$). An **infinitary species** (inspecies) is an infinitary genus containing no strictly smaller infinitary genus.

**Theorem.** Under (A1)–(A4):

1. At least one inspecies exists.
2. If $C$ is an inspecies, every individual of $C$ has a descendant in every infinite subset of $C$; in particular every individual of $C$ is an ancestor of almost every member of $C$.
3. (Morphological trichotomy.) For any property $P$ of individuals and inspecies $C$, exactly one holds: $P$ holds for almost every member of $C$; $P$ fails for almost every member of $C$; or every member of $C$ has both a descendant satisfying $P$ and a descendant failing $P$.
4. Two inspecies with infinite intersection are equal.
5. (Dual Knight–Darwin law.) If moreover $G$ has no infinite directed path of individuals each with fewer than $2$ parents (the graph-theoretic Knight–Darwin law: no perpetual self-fertilization), then no inspecies contains an infinite path of individuals each with fewer than $2$ children; infinitely many individuals have several children; and within an inspecies every individual has a pair of descendants that breed together.

## Expansion

Existence uses König's lemma and Zorn's lemma: by (A1)–(A3) the set of infinitary genera is nonempty (the whole of $V$ is one), and the intersection of a decreasing chain of infinitary genera is again infinite and ancestrally closed, because finitely many roots, finite offspring numbers and the birthdate condition make the relevant ancestry trees locally finite; a minimal element is an inspecies. Minimality forces property 2: if some member had no descendant in an infinite subset $S$, the ancestral closure of $S$ would be a strictly smaller infinitary genus. The trichotomy and the intersection property follow by applying the same argument to the sets where $P$ holds or fails, and the dual law by applying minimality to the ancestral closure of an infinite path of single-child individuals.

## Sources

- Samuel Alexander, "Infinite graphs in systematic biology, with an application to the species problem", arXiv (2012); Acta Biotheoretica (2013). Sections 1 and 3–5 (assumptions A1–A4, Propositions 1–2 and 5–8, Theorems 3 and 9). <https://doi.org/10.48550/arXiv.1201.2869>. Published version: Acta Biotheoretica 61(2) (2013), 181–201, <https://doi.org/10.1007/s10441-012-9168-y>; locators above refer to the arXiv version.
