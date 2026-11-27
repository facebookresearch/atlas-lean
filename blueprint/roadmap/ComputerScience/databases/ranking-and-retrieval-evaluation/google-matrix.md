# Google matrix

Let $P$ be a real matrix with rows and columns indexed by a set $S$, let $v$ be a real column vector indexed by $S$, and let $\alpha$ be a real scalar. The **Google matrix** $G$ is defined entrywise by

$$G_{ij} = \alpha P_{ij} + (1-\alpha)v_i, \qquad G = \alpha P + (1-\alpha)v\mathbf{1}^{\mathsf T}.$$

Here $\mathbf{1}$ is the all-ones column vector, so the same $v$ appears in every column. The formula itself requires no stochasticity assumptions.

For PageRank on a finite, nonempty set of nodes, take the columns of $P$ and the teleport vector $v$ to be probability vectors: each has nonnegative entries summing to $1$. With $0<\alpha<1$, the transition from node $j$ follows column $j$ of $P$ with probability $\alpha$ and samples from $v$ otherwise. Column $j$ of $G$ is thus a convex combination of two probability vectors, so $G$ is column-stochastic. Its entry $G_{ij}$ is the probability of moving from $j$ to $i$, and a probability column vector $x$ advances to $Gx$. Entries of $v$ may be zero.

Dangling-node repair is a separate way to construct the input $P$. Start with a nonnegative link matrix $L$ whose nonzero columns sum to $1$. Keep those columns and replace each zero column (a node with no outgoing links) by $v$. The resulting $P$ is column-stochastic. This is the *strongly preferential* choice: a dangling node uses the same distribution as teleportation. A weakly preferential model chooses its replacement independently of $v$, for example the uniform distribution.

## Sources

- D. F. Gleich, *PageRank beyond the Web*, SIAM Review 57(3) (2015), 321–363. In the [arXiv manuscript](https://arxiv.org/abs/1407.5107v1), see equation (2.1) and Definition 2.1 (p. 2) for the matrix and probability assumptions, and Theorem 2.5 (p. 4) for the column correction $vc^{\mathsf T}$, where $c_j$ is the missing mass in column $j$. Section 3.1 (pp. 6–7) describes the two choices at dangling nodes; its displayed outer products are transposed relative to the column convention above.
