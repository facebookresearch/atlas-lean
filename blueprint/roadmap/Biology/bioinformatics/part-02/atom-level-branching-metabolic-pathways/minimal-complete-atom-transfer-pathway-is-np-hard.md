# Minimal complete atom-transfer pathway is NP-hard

Let $\mathcal{R}$ be a finite set of reactions over a set of metabolites, where each metabolite consists of distinct atom positions and $\mathcal{A}$ is the set of all atom positions. Each reaction $r$ carries an **atom mapping** $\Gamma(r) \subseteq \mathcal{A} \times \mathcal{A}$ sending substrate atoms to product atoms (a reversible reaction is modelled as two reactions). For $P \subseteq \mathcal{R}$, the **atom graph** $G(P)$ has vertex set $\mathcal{A}$ and an edge $a \to a'$ for every $(a, a') \in \Gamma(r)$, $r \in P$. The pathway $P$ **transfers** $s$ to $t$ if $G(P)$ has a directed path $s \to t$; write $f_P(S)$ for the atoms reachable from a set $S$. For source and target atom sets $S, T \subseteq \mathcal{A}$ define the score

$$Z_O(P, S, T) = \frac{|f_P(S) \cap T|}{|T|},$$

the fraction of target atoms derivable from source atoms; $P$ is **complete** if $Z_O = 1$. Pathways may branch: different target atoms may be reached along different reaction chains.

**Problems.** *Find-Branching-Pathways*: given $\mathcal{R}$, $S$, $T$, an integer $l$ and a threshold $w$, list all $P \subseteq \mathcal{R}$ with $Z_O(P, S, T) \ge w$ and $|P| < l$. *Find-Minimal-Pathway*: find such a $P$ of minimum cardinality.

**Lemma.** Find-Minimal-Pathway is NP-hard, already for $w = 1$ (complete pathways) and atom mappings that are matchings. **Corollary.** Find-Branching-Pathways is NP-hard.

## Expansion

Reduce from Minimum Set Cover. Given a universe $\{s_1, \dots, s_k\}$ and subsets $C_1, \dots, C_q$, create two atoms $a_j, a_j'$ per element, one reaction $r_i$ per subset with $\Gamma(r_i) = \{ (a_j, a_j') : s_j \in C_i \}$, sources $S = \{a_j\}$, targets $T = \{a_j'\}$ and $w = 1$. A pathway is complete exactly when its reactions' subsets cover the universe, and $|P|$ equals the cover size, so a minimum complete pathway is a minimum set cover. Enumerating all solutions of Find-Branching-Pathways and taking the smallest solves Find-Minimal-Pathway, giving the corollary. In practice the ReTrace heuristic grows a pathway by repeatedly attaching $k$ shortest atom-graph paths (Yen's algorithm) from already-reached atoms to unresolved target atoms; with recursion depth at most $|T|$ it runs in $O\big(k|T|\,(n(m + n\log n) + |T|)\big)$ time on an atom graph with $n$ vertices and $m$ edges.

## Sources

- E. Pitkänen, P. Jouhten and J. Rousu, "Inferring branching pathways in genome-scale metabolic networks", BMC Systems Biology 3 (2009) 103, Methods (definitions of atom graph and $Z_O$), Computational Problems 1–2, Lemma 1, Corollary 1 and Lemma 2, <https://doi.org/10.1186/1752-0509-3-103>, PMCID PMC2791103.
