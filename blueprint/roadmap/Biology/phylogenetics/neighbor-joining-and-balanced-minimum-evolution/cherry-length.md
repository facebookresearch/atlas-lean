# Balanced minimum-evolution length of a cherry tree

For a finite set $S$ of clusters, a real cluster dissimilarity $D$ and clusters $a, b$, put

$$L_{ab} = \frac12 \sum_{\substack{u, v \in S\\ u \ne v}} c_{ab}(u, v)\, D(u, v),$$

where $c_{ab}$ is the [generalized Pauplin coefficient](cherry-coeff.md). For symmetric $D$ it is $\sum_{u < v} c_{ab}(u, v) D(u, v)$, the balanced minimum-evolution length of $T_{ab}$.
