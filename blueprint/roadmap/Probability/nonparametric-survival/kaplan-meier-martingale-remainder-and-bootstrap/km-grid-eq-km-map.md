# Kaplan–Meier as a function of the indicator mean

Fix strictly increasing grid times $t_j$ and encode an observation $(T, \delta)$ by the indicators of a death at $t_j$ and of being at risk at $t_j$; for a vector $\theta$ of such coordinates let $\mathrm{KM}(\theta)_j = \prod_{l\le j}(1 - \theta(\text{death}, l)/\theta(\text{risk}, l))$. If the first $n$ observed times lie on the grid, then $\hat S_n(t_j) = \mathrm{KM}(\bar x_n)_j$, with $\bar x_n$ the mean of the encoded observations.
