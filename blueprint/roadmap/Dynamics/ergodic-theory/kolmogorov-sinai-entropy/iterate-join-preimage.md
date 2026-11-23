# Dynamical refinement commutes with pullback along a factor map

Let $T : X \to X$, $S : Y \to Y$ and $\pi : X \to Y$ be maps with $\pi \circ T = S \circ \pi$. For every family
$\eta = (D_i)_{i \in I}$ of subsets of $Y$, every $n \ge 0$ and every word $w \in I^n$, the atom of $w$ in the
[dynamical refinement](iterate-join.md) of the pulled-back family $\pi^{-1}\eta = (\pi^{-1} D_i)_{i \in I}$ under
$T$ is the preimage under $\pi$ of the atom of $w$ in the dynamical refinement of $\eta$ under $S$:

$$\bigcap_{k < n} T^{-k} \pi^{-1} D_{w_k} = \pi^{-1} \bigcap_{k < n} S^{-k} D_{w_k}.$$
