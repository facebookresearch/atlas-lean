# Online play has mean zero against random signs

Let $A$ be a deterministic online algorithm, $T \in \mathbb{N}$ and $t \in \{0,\dots,T-1\}$ a round. For a sign sequence $\sigma : \mathrm{Fin}\,T \to \{\text{true},\text{false}\}$ write $s_t(\sigma) = +1$ if $\sigma_t$ is true and $-1$ otherwise, and $x_t(\sigma) = A_t(\sigma_0,\dots,\sigma_{t-1})$ for the play at round $t$. Then, summing over all $2^T$ sign sequences,

$$\sum_{\sigma \in \{\text{true},\text{false}\}^T} s_t(\sigma)\, x_t(\sigma) = 0 .$$

Flipping coordinate $t$ negates $s_t$ and leaves the play unchanged, so the sum equals its own negation.
