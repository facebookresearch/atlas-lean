# Finite-horizon passivity of a network trajectory

Let a lumped network plant have $n_N$ nodes, $n_B$ branches, incidence matrix $B \in \mathbb{R}^{n_N \times n_B}$, and branch sets $\mathcal{R}, \mathcal{L}, \mathcal{C}, \mathcal{S}$ (resistors, inductors, capacitors, sources) partitioning the branches, with resistances $R_e$, inductances $L_e$ and capacitances $C_e$. A trajectory consists of node potentials $\varphi(t)$, node injections $j(t)$, branch voltages $v(t)$ and branch currents $i(t)$. Its storage, supply rate and loss rate are

$$E(t) = \sum_{e \in \mathcal{C}} \tfrac12 C_e v_e(t)^2 + \sum_{e \in \mathcal{L}} \tfrac12 L_e i_e(t)^2, \quad P(t) = \varphi(t)\cdot j(t) - \sum_{e \in \mathcal{S}} v_e(t)\, i_e(t), \quad D(t) = \sum_{e \in \mathcal{R}} R_e\, i_e(t)^2.$$

Assume $R_e \ge 0$ for $e \in \mathcal{R}$, $L_e > 0$ for $e \in \mathcal{L}$ and $C_e > 0$ for $e \in \mathcal{C}$. Let the trajectory obey, at every time, the network laws: $v = B^{\mathsf T}\varphi$, $B\,i = j$, $v_e = R_e i_e$ for $e \in \mathcal{R}$, $i_e = C_e v_e'$ for $e \in \mathcal{C}$, $v_e = L_e i_e'$ for $e \in \mathcal{L}$, with $v_e$ differentiable for $e \in \mathcal{C}$ and $i_e$ differentiable for $e \in \mathcal{L}$. Then for every $a \le b$ such that $P$ is continuous on $[a, b]$ and $P - D$ is interval integrable on $[a, b]$,

$$E(b) - E(a) \le \int_a^b P(s)\,ds.$$
