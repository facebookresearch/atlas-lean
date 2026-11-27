# Orientation of ordered scaffolds: NP-hardness and tractable cases

**Setting.** A draft genome consists of scaffolds $s_1,\dots,s_n$ whose order along the chromosomes is known (for instance from FISH or Hi-C), while their strands may be unknown. An *assembly* $\mathcal A$ is a set of *assembly points* (adjacencies) $p=(s_i,s_j)$. Each point is *oriented*, *semi-oriented* or *unoriented* according to whether the strands of both, one or neither of its scaffolds are specified. A *realization* fixes every unknown strand. It is *non-conflicting* if, in the scaffold assembly graph (vertices $s^h,s^t$ for scaffold heads and tails, directed scaffold edges $s^t\to s^h$, and undirected adjacency edges), every vertex has at most one adjacency. Let $\overline{\mathcal R}(\mathcal A)$ denote the non-conflicting realizations.

- $\overline{\mathcal R}(\mathcal A)\ne\varnothing$ iff $\mathcal A$ is non-conflicting or semi-conflicting and its orientation graph $\mathrm{OG}(\mathcal A)$ is non-branching. In that case $|\overline{\mathcal R}(\mathcal A)|=2^{|S_u(\mathcal A)|}$, where $S_u(\mathcal A)$ is the set of scaffolds of unknown orientation.

**Problem (OOS).** Given $\mathcal A$ with $\overline{\mathcal R}(\mathcal A)\ne\varnothing$ and a (weighted) set $\mathcal O$ of assembly points on its scaffolds, from paired-end reads, long reads or homology, find $\bar{\mathcal A}\in\overline{\mathcal R}(\mathcal A)$ maximizing the total weight of points of $\mathcal O$ whose orientation is consistent with $\bar{\mathcal A}$, i.e. realized by a path in the scaffold assembly graph of $\bar{\mathcal A}$ with matching end directions.

**Theorem.**

*(1)* OOS is NP-hard, already when $\mathcal A$ is a linear genome or a circular genome with unknown scaffold orientations.

*(2)* OOS decomposes over connected components of $\mathrm{OG}(\mathcal A)$: concatenating optimal solutions of the sub-instances gives an optimal solution.

*(3)* (Non-branching OOS) If the constraint graph $\mathrm{COG}(\mathcal O)$ is non-branching, so that each scaffold's orientation is constrained relative to at most two others, OOS is solvable in polynomial time.

*(4)* (FPT algorithm) In general OOS can be solved in time

$$O\big(2^{\alpha}\,|S(\mathcal A)|^2\,|\mathrm{CC}(\mathcal O)|\big),\qquad \alpha=\max_{c\in\mathrm{CC}(\mathcal O)}|\mathrm{BV}(\mathcal O)\cap V(c)|,$$

where the sets are those of §3.5: $\mathrm{BV}(\mathcal O)$ is the set of unoriented branching vertices (unoriented vertices of degree greater than $2$) of $\mathrm{COG}(\mathcal O)$; $\mathrm{AV}(\mathcal O)\subseteq\mathrm{BV}(\mathcal O)$ is the set of unoriented articulation vertices of degree at least $3$; breaking $\mathrm{COG}(\mathcal O)$ at the vertices of $\mathrm{AV}(\mathcal O)$, with a copy of each such vertex in every resulting component, gives a set of components, and $\mathrm{CC}(\mathcal O)$ is the set of those components that contain at least one cycle; $V(c)$ is the vertex set of a component $c$.

## Expansion

Once the order is fixed, each scaffold contributes one binary variable (its strand), and each constraint in $\mathcal O$ asks two of these variables to be equal or different. OOS is therefore a weighted maximum-agreement problem on signed pairwise constraints. This explains why the problem is hard in general and why constraints that form only paths and cycles can be optimized by dynamic programming along them. Branching vertices are where paths meet, and guessing their orientations ($2^\alpha$ choices per component) splits the remaining structure into non-branching pieces. The results are implemented in the CAMSA framework for comparative scaffold assembly.

## Sources

- Sergey Aganezov, Pavel Avdeyev, Nikita Alexeev, Yongwu Rong and Max A. Alekseyev, "Orienting Ordered Scaffolds: Complexity and Algorithms", arXiv:1911.11190 (2019), Section 2 (assemblies, realizations, Theorem 2, Corollary 3), Section 3 (problems OOS and NOOS, Theorem 8), Theorems 10, 12–14 and 16, <https://doi.org/10.48550/arXiv.1911.11190>.
