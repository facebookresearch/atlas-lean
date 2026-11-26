# Reverse-search tree with monotone module density

**Setting.** Let $V$ be the proteins of an interaction network with symmetric weights $W = (w_{ij})$, $0 \le w_{ij} \le 1$ ($w_{ij} = 0$ for missing edges). For a module $U \subseteq V$ with $|U| \ge 2$, the **density** is the average pairwise weight

$$\rho_W(U) = \frac{\sum_{\{i,j\} \subseteq U,\ i \ne j} w_{ij}}{\binom{|U|}{2}}, \qquad \rho_W(U) := 1 \text{ if } |U| = 1,$$

and the **weighted degree** of $u \in U$ within $U$ is $\deg_W(u, U) = \sum_{v \in U \setminus \{u\}} w_{uv}$. *Dense module enumeration*: given $\theta > 0$, list all $U \subseteq V$ with $\rho_W(U) \ge \theta$.

**Lemma.** If $v \in U$ has minimum weighted degree in $U$ ($|U| \ge 3$), then $\rho_W(U \setminus \{v\}) \ge \rho_W(U)$.

**Search tree.** Fix a strict total order $\operatorname{ord}$ on $V$. The **parent** of a module $U^\ast$ with $|U^\ast| \ge 1$ is obtained by deleting, among its nodes of minimum weighted degree in $U^\ast$, the one with smallest $\operatorname{ord}$; equivalently $U^\ast = U \cup \{v\}$ is a child of $U$ iff for every $u \in U$, either $\deg_W(v, U^\ast) < \deg_W(u, U^\ast)$, or the degrees are equal and $\operatorname{ord}(v) < \operatorname{ord}(u)$.

**Theorem.** The parent relation makes the set of all modules a rooted tree with root $\emptyset$, and density is non-increasing along every root-to-leaf path (from size $2$ on). Hence the depth-first traversal that, from each module $U$ with $\rho_W(U) \ge \theta$, tests every $U \cup \{v\}$ ($v \notin U$) for being a child of $U$ and recurses only into children satisfying the threshold outputs every module with $\rho_W(U) \ge \theta$ exactly once, with polynomial delay between consecutive outputs.

## Expansion

Let $k = |U|$ and $S = \sum_{\{i,j\}\subseteq U} w_{ij}$, so $\rho_W(U) = 2S/(k(k-1))$ and $\sum_{u \in U} \deg_W(u,U) = 2S$. The minimum degree is at most the mean, $\deg_W(v, U) \le 2S/k$, so

$$\rho_W(U\setminus\{v\}) = \frac{2\big(S - \deg_W(v,U)\big)}{(k-1)(k-2)} \ \ge\ \frac{2S(1 - 2/k)}{(k-1)(k-2)} = \frac{2S}{k(k-1)} = \rho_W(U).$$

Every nonempty module has exactly one parent of size one less, so iterating the parent map reaches $\emptyset$ and the relation is a tree; by the lemma a module below threshold has no descendant above it, which justifies pruning. Ordinary superset-closure pruning fails because a superset of a module can be denser or sparser. Additional data enter as constraints that are themselves monotone along the tree, for example requiring all members to share a binary condition profile on at least a given number of conditions (a property inherited by every subset), so the same traversal enumerates dense, condition-consistent modules; a module none of whose one-node extensions meets the threshold is reported as locally maximal at no extra cost.

## Sources

- E. Georgii, S. Dietmann, T. Uno, P. Pagel and K. Tsuda, "Enumeration of condition-dependent dense modules in protein interaction networks", Bioinformatics 25 (2009), 933–940, Section 2 (Eq. (1), Definitions 1–3, Lemma 1, Algorithm 1), <https://doi.org/10.1093/bioinformatics/btp080>, PMCID: PMC2660875.
- D. Avis and K. Fukuda, "Reverse search for enumeration", Discrete Applied Mathematics 65 (1996), 21–46.
