# Network storage balance

Let $B \in \mathbb{R}^{n_N \times n_B}$ be a node-branch matrix and let the branches be split by sets $\mathcal{R}, \mathcal{L}, \mathcal{C}, \mathcal{S}$ that are pairwise disjoint and cover all branches, with values $R_e \ge 0$ on $\mathcal{R}$, $L_e > 0$ on $\mathcal{L}$ and $C_e > 0$ on $\mathcal{C}$. For node potentials $\varphi(s)$, node injections $j(s)$, branch voltages $v(s)$ and branch currents $i(s)$, let

$$E(s) = \sum_{e \in \mathcal{C}} \frac{C_e v_e(s)^2}{2} + \sum_{e \in \mathcal{L}} \frac{L_e i_e(s)^2}{2}, \qquad P_S(s) = \sum_{e \in \mathcal{S}} v_e(s)\,i_e(s), \qquad P_R(s) = \sum_{e \in \mathcal{R}} R_e\,i_e(s)^2.$$ Suppose that at time $t$: $v(t) = B^\top \varphi(t)$, $B\,i(t) = j(t)$, $v_e = R_e i_e$ on $\mathcal{R}$, $i_e = C_e v_e'$ on $\mathcal{C}$, $v_e = L_e i_e'$ on $\mathcal{L}$, with $v_e$ differentiable at $t$ for $e \in \mathcal{C}$ and $i_e$ differentiable at $t$ for $e \in \mathcal{L}$. Then
$$E'(t) = \varphi(t) \cdot j(t) - P_S(t) - P_R(t).$$
