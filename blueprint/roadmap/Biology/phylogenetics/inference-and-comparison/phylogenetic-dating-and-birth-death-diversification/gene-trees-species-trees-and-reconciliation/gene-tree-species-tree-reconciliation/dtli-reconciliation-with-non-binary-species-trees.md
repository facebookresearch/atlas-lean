# DTLI reconciliation with non-binary species trees

**Input.** A rooted binary gene tree $T_G = (V_G, E_G)$, a rooted species tree $T_S = (V_S, E_S)$ that may contain polytomies, and a leaf map $M_L$ from sampled genes to the species they were sampled from. For a tree node $v$, $C(v)$ and $P(v)$ denote its children and parent.

**Reconciliation.** A reconciliation $R_{GS}$ assigns to every internal gene node $g$ a species $M(g) \in V_S$ and an event in $\{\mathrm{D}, \mathrm{T}, \mathrm{S}, \mathrm{I}\}$ (duplication, transfer, speciation, deep coalescence), and to every non-root gene node the losses on the edge from $P(g)$ to $g$. An edge $(u, v)$ is a transfer edge when the event at $u$ is a transfer and $M(u)$ and $M(v)$ are incomparable in $T_S$; the transfer goes from donor $M(u)$ to recipient $M(v)$.

**Cost.** With costs $\delta, \lambda, \tau > 0$ and counts $D$, $L$, $T$ of duplications, losses and transfers,

$$\pi(R_{GS}) = \delta D + \lambda L + \tau T \qquad \text{(Eq. 1)};$$

speciations (co-divergence at binary species nodes) and deep coalescences (co-divergence at polytomies) cost $0$.

**Model constraint (when lineage sorting suffices).** Let $g$ have children $c_1, c_2$ and $M(g) = s$. The divergence at $g$ is a co-divergence with $s$ iff each child lineage of $s$ vertically inherits at most one descendant of $g$, i.e. the sets $\Delta(c_1), \Delta(c_2) \subseteq C(s)$ of children of $s$ that vertically inherit descendants of $c_1$ and of $c_2$ are disjoint; if they intersect, $g$ is a duplication (Eq. 2). Equivalently, a deep coalescence is inferred exactly when the gene tree's branching below $g$ is consistent with some binary resolution of the polytomy $s$. When $s$ is binary, Eq. 2 reduces to the classical least-common-ancestor test for duplications.

**Problem.** Output all reconciliations minimizing $\pi$ subject to the model constraint that are also temporally feasible (no transfer between non-contemporaneous lineages). For fixed maximum polytomy out-degree $k^*$, a two-pass dynamic program (post-order cost tables over all candidate $M(g)$ and all bipartitions of $C(s)$, then traceback) runs in $O(h_S\,|V_G|\,|V_S|^2)$ time, $h_S$ the height of $T_S$.

## Expansion

At a binary species node, any incongruence must come from duplication or transfer, because lineage sorting across a long branch is assumed negligible. At a polytomy, every binary resolution is a hypothesis of rapid speciation, and a gene subtree consistent with one of them is explained at no cost by lineage sorting; only when two descendants of $g$ must pass through the same child lineage of $s$ is an additional locus required. Transfers make $M(g)$ non-local (genes jump across the species tree), and an optimal history may require a locally suboptimal choice at an internal node, so all assignments must be kept in the tables and several optimal histories can exist; the source finds inconsistent optimal histories for 20% of 1128 cyanobacterial gene trees, and that ignoring lineage sorting inflates inferred duplications and transfers.

## Sources

- M. Stolzer, H. Lai, M. Xu, D. Sathaye, B. Vernot, D. Durand, "Inferring duplications, losses, transfers and incomplete lineage sorting with nonbinary species trees", Bioinformatics 28(18) (2012) i409–i415, Sections 1.3–2.3, Eqs. 1–2, <https://doi.org/10.1093/bioinformatics/bts386> (PMC3436813).
