# Product of coordinate weights off one coordinate

Let $E$ be a finite set, $p \in \mathbb{R}$, $e \in E$ and $\omega \in \{0,1\}^E$. The weight of $\omega$ off $e$ is the product of the [coordinate weights](edge-weight.md) over all coordinates other than $e$:

$$W_p^{(e)}(\omega) = \prod_{j \in E,\ j \ne e} w_p(\omega, j).$$
