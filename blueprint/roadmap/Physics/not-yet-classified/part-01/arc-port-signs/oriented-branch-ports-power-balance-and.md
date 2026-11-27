# Power balance and branch reversal

Let $V$ and $E$ be finite sets of nodes and branches, each branch $e$ having a tail and a head node, and let $\mathcal{A} \in \mathbb{R}^{V \times E}$ be the electrical incidence matrix, $\mathcal{A}_{n e} = [\mathrm{tail}(e) = n] - [\mathrm{head}(e) = n]$. Let $\varphi, j : V \to \mathbb{R}$ and $v, i : E \to \mathbb{R}$ satisfy $\mathcal{A}\,i = j$ and $v = \mathcal{A}^\top \varphi$, and fix a branch $e_0$. Let $\mathcal{A}'$ be the incidence matrix after swapping the tail and head of $e_0$, and let $i'$ and $v'$ agree with $i$ and $v$ except $i'_{e_0} = -i_{e_0}$ and $v'_{e_0} = -v_{e_0}$. Then

$$\sum_{e \in E} v_e\,i_e = \sum_{n \in V} \varphi_n\,j_n, \qquad \mathcal{A}'\,i' = j, \qquad \mathcal{A}'^{\top} \varphi = v'.$$
