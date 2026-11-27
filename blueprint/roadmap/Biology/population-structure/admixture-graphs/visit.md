# Probability that a lineage passes through a node

In an [admixture graph](admixture-graph.md) with parents $\mathrm{pa}$ and admixture proportions $a$, the visit probability $v(X, c)$ of a node $c$ from a node $X$ is defined by well-founded recursion along the parent relation:

$$v(X, c) = \begin{cases} 1 & X = c,\\ \sum_{Y \in \mathrm{pa}(X)} a(X, Y)\, v(Y, c) & X \ne c. \end{cases}$$

It is the probability that the lineage of a gene sampled in $X$, traced toward the root with parents chosen according to the admixture proportions, passes through $c$.
