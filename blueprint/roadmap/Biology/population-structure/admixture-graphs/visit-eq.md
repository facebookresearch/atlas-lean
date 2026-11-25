# First-step equation for visit probabilities

In every [admixture graph](admixture-graph.md) and for all nodes $X, c$, the [visit probability](visit.md) satisfies

$$v(X, c) = \begin{cases} 1 & X = c,\\ \sum_{Y \in \mathrm{pa}(X)} a(X, Y)\, v(Y, c) & X \ne c. \end{cases}$$
