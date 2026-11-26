# Jacobian matrix of a map between Euclidean spaces

For a map $F : \mathbb{R}^P \to \mathbb{R}^n$ between Euclidean spaces and parameters $\theta \in \mathbb{R}^P$, the Jacobian $J_F(\theta)$ is the real $n \times P$ matrix (rows indexed by $\mathrm{Fin}\,n$, columns by $\mathrm{Fin}\,P$) whose $(i, p)$ entry is the directional derivative of the $i$-th output coordinate along the $p$-th standard basis vector $e_p$:

$$J_F(\theta)_{ip} = \frac{d}{dt}\Big|_{t=0} F(\theta + t\, e_p)_i .$$

When the one-variable function $t \mapsto F(\theta + t e_p)_i$ is not differentiable at $0$, the entry is $0$ (the convention for derivatives of non-differentiable functions).
