# Current injected at a node

For natural numbers $n_N$ and $n_E$, a real $n_N \times n_E$ matrix $B$, node voltages
$V \in \mathbb{C}^{n_N}$, branch admittances $y \in \mathbb{C}^{n_E}$, shunt admittances
$y^s \in \mathbb{C}^{n_N}$ and a node $v$, the current injected at $v$ is

$$I_v = \sum_{e} B_{ve}\, y_e d_e + y^s_v V_v,$$

where $d_e$ is the [branch drop](branch-drop.md) and $y_e d_e$ the current of branch $e$. When $B$
is the signed node–branch incidence matrix, the same coefficients $B_{ve}$ form the drops and
assemble this sum, so $I_v$ is the current leaving node $v$ into its incident branches and its
shunt.
