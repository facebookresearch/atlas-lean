# Play of a deterministic online algorithm at a round

A deterministic online algorithm is a family $A = (A_t)_{t \in \mathbb{N}}$ of maps $A_t : \{\text{true},\text{false}\}^t \to \mathbb{R}$. Given a sign sequence $\sigma : \mathrm{Fin}\,T \to \{\text{true},\text{false}\}$ of length $T$ and a round $t \in \{0, \dots, T-1\}$, the play at round $t$ is $A_t$ applied to the first $t$ signs:

$$\mathrm{play}_A(\sigma, t) = A_t(\sigma_0, \dots, \sigma_{t-1}) \in \mathbb{R}.$$

The algorithm never sees the current sign $\sigma_t$ or later ones.
