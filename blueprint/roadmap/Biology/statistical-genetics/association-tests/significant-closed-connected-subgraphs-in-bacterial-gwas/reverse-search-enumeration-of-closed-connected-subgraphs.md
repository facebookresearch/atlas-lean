# Reverse-search enumeration of closed connected subgraphs

**Setting.** Let $G = (V, E)$ be a connected graph whose vertices are binary covariates over $n$ samples, with $I(v) \subseteq [n]$ the samples containing $v$. For a connected subgraph $S$ put $I(S) = \bigcup_{v \in S} I(v)$ and $J(S) = \bigcap_{v \in S} I(v)$. Let $V_i = \{v : i \in I(v)\}$, let $\mathrm{Ne}(S)$ be the vertices outside $S$ adjacent to $S$, and let $\mathcal{C}$ be the set of closed connected subgraphs (CCSs): connected $S$ such that adding any neighbour changes $I(S)$. Fix arbitrary numberings of samples and vertices.

**Reduction (parent map).** For $S \in \mathcal{C}$: if $I(S) = J(S)$, then $P(S) = \emptyset$. Otherwise let

$$i_S = \max\{i : i \in I(S) \setminus J(S)\},$$

the largest sample containing some but not all units of $S$. Define $P(S)$ as the connected component of $S \setminus V_{i_S}$ that contains the largest vertex $\max\{v : v \in S \setminus V_{i_S}\}$.

**Lemma (valid reduction).** $P$ maps $\mathcal{C}$ to $\mathcal{C} \cup \{\emptyset\}$ with $P(S) \subsetneq S$, so iterating $P$ reaches $\emptyset$. Hence $P$ defines a tree on $\mathcal{C}$ rooted at the empty subgraph, in which every CCS strictly contains its parent.

**Lemma (child test without connectivity).** For $S, S' \in \mathcal{C}$ with $S \subset S' \ne \emptyset$, $S = P(S')$ if and only if

- (C1) $i_{S'} \notin I(S)$;
- (C2) $\max\{v' : v' \in S' \setminus V_{i_{S'}}\} = \max\{v : v \in S\}$;
- (C3) $(S' \setminus V_{i_{S'}}) \cap \mathrm{Ne}(S) = \emptyset$.

None of these conditions requires computing the connected components of $S' \setminus V_{i_{S'}}$.

**Theorem (inverting the reduction).** Children are generated from equivalence groups of neighbours, i.e. neighbours $v_1, v_2$ with $I(S \cup \{v_1\}) = I(S \cup \{v_2\})$. Recursion then runs from each child found through the neighbours of that child, with a local table of already-enumerated patterns $I$ to stop repeats. Started from $S$, this procedure returns exactly $\{S' \in \mathcal{C} : P(S') = S\}$, each child once.

**Consequence.** Traversing this tree from $\emptyset$ enumerates every CCS exactly once. No global item table or articulation-point bookkeeping is needed, and every explored CCS contains the one it was reached from. That last property is what makes superset pruning by minimal attainable p-values valid.

## Depends on

- [Tarone testability pruning for closed connected subgraphs](tarone-testability-pruning-for-closed-connected-subgraphs.md)

## Expansion

This is reverse search in the sense of Avis and Fukuda. A reduction that returns a unique strictly smaller element defines a tree, and enumeration only needs a way to list the preimages of a node. Here $P$ deletes every unit carried by the last sample that distinguishes $S$ internally, then keeps a canonical component. Because only one component is kept, a child $S'$ of $S$ need not be reachable from $S$ by adding one neighbour and closing. In a four-vertex example, both $\{v_1, v_3, v_4\}$ and $\{v_1, v_2, v_3, v_4\}$ reduce to $\{v_3\}$ through the intermediate child $\{v_3, v_4\}$. The recursion through children's neighbours therefore reconnects components that the reduction discards. The pattern table then removes duplicates: a candidate whose pattern contains an already-enumerated sibling pattern has been visited. Conditions (C1)–(C3) check the candidate in time independent of component structure, which is what lets the method scale to bacterial pan-genome graphs.

## Sources

- H. Roux de Bézieux, L. Lima, F. Perraudeau, A. Mary, S. Dudoit, L. Jacob, "CALDERA: finding all significant de Bruijn subgraphs for bacterial GWAS", Bioinformatics 38 (2022) i36–i44, Section 3.2, Definition 2, Lemmas 2–3, Algorithm 1, Theorem 1 and the example of Section 3.3, <https://doi.org/10.1093/bioinformatics/btac238> (PMC9235473).
