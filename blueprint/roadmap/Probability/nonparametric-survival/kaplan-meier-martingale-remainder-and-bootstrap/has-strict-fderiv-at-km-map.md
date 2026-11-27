# Smoothness of the Kaplan–Meier map

Fix grid times $t_j$ and encode an observation $(T, \delta)$ by the indicators of a death at $t_j$ and of being at risk at $t_j$; for a vector $\theta$ of such coordinates let $\mathrm{KM}(\theta)_j = \prod_{l\le j}(1 - \theta(\text{death}, l)/\theta(\text{risk}, l))$. If every at-risk coordinate of $\theta$ is nonzero, $\mathrm{KM}$ is strictly differentiable at $\theta$.
