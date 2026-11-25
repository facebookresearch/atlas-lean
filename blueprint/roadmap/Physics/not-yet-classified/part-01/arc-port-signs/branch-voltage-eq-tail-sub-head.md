# Branch voltage from node potentials

Let $V$ and $E$ be finite sets of nodes and branches, each branch $e$ having a tail and a head node, and let $\mathcal{A} \in \mathbb{R}^{V \times E}$ be the electrical incidence matrix, $\mathcal{A}_{n e} = [\mathrm{tail}(e) = n] - [\mathrm{head}(e) = n]$. If the branch voltages are $v = \mathcal{A}^\top \varphi$ for node potentials $\varphi : V \to \mathbb{R}$, then for every branch $e$

$$v_e = \varphi(\mathrm{tail}(e)) - \varphi(\mathrm{head}(e)).$$
