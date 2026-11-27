# Forward checking preserves solutions

Let $\sigma$ be a solution of a binary constraint satisfaction problem within finite domains $\mathrm{dom}$: $\sigma(x) \in \mathrm{dom}(x)$ for all $x$ and every constraint arc allows the values of $\sigma$. For any variable $x$, forward checking after assigning $x = \sigma(x)$ (restrict $x$ to $\{\sigma(x)\}$ and every variable joined to $x$ by an arc to the values compatible with $\sigma(x)$) gives domains within which $\sigma$ is still a solution.
