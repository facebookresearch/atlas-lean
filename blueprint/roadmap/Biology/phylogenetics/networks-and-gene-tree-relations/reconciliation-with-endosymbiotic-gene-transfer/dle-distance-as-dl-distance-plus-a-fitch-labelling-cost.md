# DLE-distance as DL-distance plus a Fitch labelling cost

**Setting.** Let $S$ be a rooted binary species tree on species $\Sigma$, each species $\sigma$ having two genomes $\sigma_0, \sigma_1$ (e.g. mitochondrial and nuclear), and let $T$ be a rooted binary gene tree whose leaves carry a species label $s(x) \in \Sigma$ and a genome label $b(x) \in \{0,1\}$. A **DLE-reconciliation** $\langle R, \tilde s, \tilde b, \tilde e\rangle$ extends $T$ to a partially binary tree $R$ (by grafting loss leaves and unary nodes) and extends $s$ and $b$ to all nodes, each binary node $x$ with children $x_l, x_r$ being a

- speciation (Spe): $\tilde s(x_l), \tilde s(x_r)$ are the two children of $\tilde s(x)$ and $\tilde b(x_l) = \tilde b(x_r) = \tilde b(x)$;
- duplication (Dup): $\tilde s(x_l) = \tilde s(x_r) = \tilde s(x)$ and $\tilde b(x_l) = \tilde b(x_r) = \tilde b(x)$;
- copy transfer (EGTcopy): $\tilde s(x_l) = \tilde s(x_r) = \tilde s(x)$ and $\tilde b(x_l) \ne \tilde b(x_r)$;

unary nodes are cut transfers (EGTcut, moving a gene to the other genome), and grafted leaves are losses. With speciations free and unit cost for every other event, the minimum cost is the **DLE-distance** $\mathrm{DLE}(T,S)$; $\mathrm{DL}(T,S)$ denotes the classical duplication–loss distance. Let $d(x) = 1$ if $x$ is a duplication in the optimal DL-reconciliation. For a binary labelling $\tilde b$ of $V(T)$ extending $b$, set $\Delta_{\tilde b}(x) = 0$ at leaves and otherwise

$$\Delta_{\tilde b}(x) = \max\big(0,\; |\tilde b(x) - \tilde b(x_l)| + |\tilde b(x) - \tilde b(x_r)| - d(x)\big), \qquad \mathrm{cost}(T, S, \tilde b) = \sum_{x \in V(T)}\Delta_{\tilde b}(x).$$

**Theorem.**
1. (LCA mapping) Every minimum-cost DLE-reconciliation has $\tilde s(x) = \mathrm{lca}_S\big(s(\ell(T[x]))\big)$ for all $x \in V(T)$.
2. (Labels) Some optimal reconciliation satisfies $\tilde b(x) \in \{\tilde b(x_l), \tilde b(x_r)\}$ at every internal node.
3. (Decomposition) $\mathrm{DLE}(T,S) = \mathrm{DL}(T,S) + \min_{\tilde b}\mathrm{cost}(T,S,\tilde b)$, and a Fitch-type two-pass algorithm on the genome labels computes $\mathrm{DLE}(T,S)$ and an optimal reconciliation in linear time.
4. (Arbitrary costs) For costs $\delta$ (duplication), $\lambda$ (loss), $\tau_b$ (EGTcopy from genome $b$) and $\rho_b$ (EGTcut from genome $b$), a dynamic program over $T$ with states $D[x, b_x]$, $b_x \in \{0,1\}$, gives the minimum cost of a reconciliation of $T[x]$ with root genome $b_x$, and $\min(D[r(T), 0], D[r(T), 1])$ is computed in time $O(|V(T)| + |V(S)|)$.

## Depends on

- [Fitch's algorithm](../../small-parsimony-problem/fitch.md)

## Expansion

Part 2 is an exchange argument: if $\tilde b(x)$ differed from both children's labels, at least one EGTcut sits on a child edge; relabelling $x$ to its children's common label removes that cut and adds at most one cut above $x$, never increasing the cost, and repeating bottom-up yields the property. Given labels on $T$, the species mapping and the placement of duplications and losses are those of the DL-reconciliation; label changes along edges cost one cut each, except that at a DL-duplication node one child's change can be absorbed by turning the duplication into an EGTcopy at no extra cost, which is the $-d(x)$ in $\Delta$. Minimizing $\sum_x \Delta_{\tilde b}(x)$ over labellings is a two-state small-parsimony problem with this correction, solved by Fitch's intersection–union rule. For general costs the LCA mapping still fixes $\tilde s$, so the dynamic program needs only the genome label of each node and the number of losses implied by the mapping, which keeps it linear.

## Sources

- Y. Anselmetti, N. El-Mabrouk, M. Lafond, A. Ouangraoua, "Gene tree and species tree reconciliation with endosymbiotic gene transfer", Bioinformatics 37 (Suppl. 1) (2021) i120–i132, Definition 1, Lemmas 1–5 and Theorem 1 (proofs in the appendix), <https://doi.org/10.1093/bioinformatics/btab328>, PMCID PMC8312264.
