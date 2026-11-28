# Regret against a sign sequence on an interval

Let $A = (A_t)_{t\in\mathbb{N}}$ be a deterministic online algorithm, $T \in \mathbb{N}$, $D, G \in \mathbb{R}$ and $\sigma : \mathrm{Fin}\,T \to \{\text{true},\text{false}\}$ a sign sequence. Write $s_t = +1$ if $\sigma_t$ is true and $s_t = -1$ otherwise, and let $x_t = A_t(\sigma_0,\dots,\sigma_{t-1})$ be the play at round $t$. The regret is

$$\mathrm{Regret}_T(A, D, G, \sigma) = \sum_{t=0}^{T-1} s_t\, G\, x_t \;+\; G \cdot \frac{D}{2} \cdot \Big|\sum_{t=0}^{T-1} s_t\Big| .$$

This is the cumulative loss of the algorithm on the linear losses $x \mapsto s_t G x$ minus the best fixed comparator on $[-D/2, D/2]$, whose loss $-\tfrac{D}{2} G \,\big|\sum_t s_t\big|$ is already evaluated (valid for $D, G \ge 0$).
