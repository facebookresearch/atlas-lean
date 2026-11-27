# Decomposition of minimal all-pairs attractor control

**Setting.** A Boolean network on variables $V = \{v_1, \dots, v_n\}$ with update functions $f = (f_1, \dots, f_n)$ has a state transition system on $S = \{0,1\}^n$; its attractors are the bottom strongly connected components, and $\mathrm{bas}(A)$ denotes the (strong) basin of attractor $A$, the states from which every trajectory reaches $A$. A **single-step control** $C \subseteq \{1, \dots, n\}$ applied to a state $s$ flips (or fixes) the variables indexed by $C$ instantaneously, producing $C(s)$, after which the network evolves freely. For sets of source attractors $\mathcal A_s$ and target attractors $\mathcal A_t$, a set $C$ is an **all-pairs control** (APC) if for all $A_s \in \mathcal A_s$, $A_t \in \mathcal A_t$ with $A_s \ne A_t$ and every $s \in A_s$ there is $C_s \subseteq C$ with $C_s(s) \in \mathrm{bas}(A_t)$. A min-APC is an APC of minimum size.

**Projections.** For a partition $V_1, \dots, V_k$ of $V$, write $s|_{V_j}$ for the projection of a state and lift it to sets; $C_j \subseteq \mathrm{ind}(V_j)$ is an APC on $V_j$ if the APC condition holds after projecting attractors and basins to $V_j$.

**Proposition 1.** If $C^{\min}$ is a min-APC of the network, then for every block $V_j$ the restriction $C^{\min} \cap \mathrm{ind}(V_j)$ is an APC on $V_j$ (not necessarily a minimum one), and

$$C^{\min} = \bigcup_{j=1}^k \big( C^{\min} \cap \mathrm{ind}(V_j) \big).$$

Consequently $\sum_j |C_j| \le |C^{\min}|$ for any choice of min-APCs $C_j$ on the blocks, and a search for a min-APC of the whole network can start from unions of block-wise min-APCs, enlarging the blocks' candidate sets to larger block APCs when no union is a valid global APC. The restriction need not be a min-APC on its block: in the source's Example 2 ($f_1 = f_2 = x_1$, $f_3 = f_4 = x_1 \vee (x_2 \wedge x_4) \vee x_3$, blocks $\{v_1, v_2\}$, $\{v_3, v_4\}$, asynchronous update) the block min-APCs are $\{1\}$ and $\{3\}$, the global ones $\{1,2,3\}$ and $\{1,3,4\}$, and $\{1,3,4\} \cap \mathrm{ind}(V_2) = \{3,4\}$ is not minimum.

## Expansion

If a perturbation of $s$ lands in $\mathrm{bas}(A_t)$, its projection lands in the projected basin, so the restriction of a global control to a block controls the projected problem; disjointness of the blocks makes the union exact. Projected basins over-approximate the true ones, so block-wise solutions give a lower bound and candidate sets but must be verified on the full network. Computing basins dominates the cost; the decomposition lets the exponential state space be explored block by block, which makes single-step control (target control from one attractor and full control between all pairs) feasible for large real-life networks and gives perturbation sets for cellular reprogramming.

## Sources

- A. Baudin, S. Paul, C. Su, J. Pang, "Controlling large Boolean networks with single-step perturbations", Bioinformatics 35(14) (2019) i558, Sections 2-3, Example 1 and Proposition 1, <https://doi.org/10.1093/bioinformatics/btz371>, PMCID PMC6612811.
