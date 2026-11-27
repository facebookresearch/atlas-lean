# Network plant storage equals network stored energy

Let $B \in \mathbb{R}^{n_N \times n_B}$ be an incidence matrix, $\mathcal{R}, \mathcal{L}, \mathcal{C}, \mathcal{S}$ a partition of the branches into resistors, inductors, capacitors and sources, and $R, L, C : \{1,\dots,n_B\} \to \mathbb{R}$ element values. Let $\varphi, j$ be node signals and $v, i$ branch signals. For the plant built from these data and the trajectory built from these signals, the plant storage at every time $t$ equals the network stored energy

$$\sum_{e \in \mathcal{C}} \tfrac12 C_e v_e(t)^2 + \sum_{e \in \mathcal{L}} \tfrac12 L_e i_e(t)^2.$$
