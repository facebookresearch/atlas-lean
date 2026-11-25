# Branch voltage drop

For a network with $n_N$ nodes and $n_E$ branches, a real incidence matrix $B \in \mathbb{R}^{n_N \times n_E}$ and complex node voltages $V \in \mathbb{C}^{n_N}$, the voltage drop across branch $e$ is

$$\Delta_e = \sum_{v=1}^{n_N} B_{ve}\, V_v,$$

with each real incidence entry read as a complex scalar.
