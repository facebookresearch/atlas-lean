# Induced partition tree and the edge map of a supermatrix

Let $X$ be a finite set of species, $|X| = n$, and let $Y_1, \dots, Y_k \subseteq X$ with $k \ge 2$ be the species sets of the $k$ partitions (genes, loci, codon positions) of a supermatrix, so that species in $X \setminus Y_i$ contribute only gaps to partition $i$ (missing data). Let $T$ be an unrooted binary phylogenetic tree on $X$.

**Definition (induced partition tree).** For a partition $Y_i$ with $|Y_i| \ge 2$, the **induced partition tree** $T|_{Y_i}$ is the tree on leaf set $Y_i$ obtained from $T$ by deleting every leaf in $X \setminus Y_i$ and suppressing resulting vertices of degree two.

**Definition (edge map).** Identify every edge $e$ of $T$ with the split $e = A \mid B$ it induces, $A, B \neq \emptyset$, $A \cap B = \emptyset$, $A \cup B = X$. Write $E$ for the edge set of $T$, $E_i$ for the edge set of $T|_{Y_i}$ and $\epsilon$ for a formal symbol "no edge". The edge map $f_i : E \to E_i \cup \{\epsilon\}$ is

$$f_i(e) \;=\; \begin{cases} (A \cap Y_i) \mid (B \cap Y_i), & A \cap Y_i \neq \emptyset \text{ and } B \cap Y_i \neq \emptyset,\\[2pt] \epsilon, & \text{otherwise.}\end{cases}$$

The definition is well posed: when both intersections are nonempty, $(A \cap Y_i) \mid (B \cap Y_i)$ is a split of $Y_i$ displayed by $T|_{Y_i}$, hence an edge of $T|_{Y_i}$; and $f_i(e) = \epsilon$ exactly when the restriction of the split to $Y_i$ is trivial, i.e. when $e$ is one of the edges destroyed by pruning and suppression.

**Definition (partial terrace).** Two species trees $T_1, T_2$ on $X$ lie on one **partial terrace** if $T_1|_{Y_j} = T_2|_{Y_j}$ for every $j$ in some nonempty $J \subseteq \{1, \dots, k\}$, and on one **full terrace** if this holds with $J = \{1, \dots, k\}$.

## Remarks

Pruning the species of $X \setminus Y_i$ from $T$ maps the split $A \mid B$ of $X$ to the set pair $(A \cap Y_i, B \cap Y_i)$; suppression of degree-two vertices removes precisely those edges for which one side of the pair is empty, and merges all edges of $T$ whose restricted splits coincide into the single edge of $T|_{Y_i}$ carrying that split. Hence $f_i$ is surjective onto $E_i$ but in general not injective: a whole path of $T$ collapses to one edge of $T|_{Y_i}$. The collection $F = \{f_1, \dots, f_k\}$ together with $T$ and $T|_{Y_1}, \dots, T|_{Y_k}$ is the terrace-aware data structure; its purpose is that the score of partition $i$ depends on $T$ only through $T|_{Y_i}$ with its edge lengths. Under the edge-unlinked partition model, where each partition tree has its own freely optimized edge lengths, trees sharing an induced partition tree therefore share that partition's optimal score. Under edge-linked models the induced edge lengths are sums of edge lengths of $T$ over the fibres of $f_i$, which can change when $T$ changes even though $T|_{Y_i}$ does not, so equal induced topologies do not by themselves give equal scores.

## Sources

- O. Chernomor, A. von Haeseler and B. Q. Minh, "Terrace aware data structure for phylogenomic inference from supermatrices", Systematic Biology 65 (2016), 997–1008, Background section and Eq. (2), <https://doi.org/10.1093/sysbio/syw037>, PMCID: PMC5066062.
- M. J. Sanderson, M. M. McMahon and M. Steel, "Terraces in phylogenetic tree space", Science 333 (2011), 448–450.
