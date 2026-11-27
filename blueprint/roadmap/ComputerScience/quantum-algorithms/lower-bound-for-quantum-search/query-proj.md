# Query projection

Let $\iota$ and $W$ be finite sets and $O_y$ the [phase oracle marking](marking-oracle.md) $y \in \iota$ on $\ell^2(\iota \times W)$. The query projection is the linear map

$$P_y = \tfrac12\,(I - O_y),$$

which keeps the amplitudes at $(y, w)$ for every $w \in W$ and zeroes the others: it is the orthogonal projection onto the basis states whose query register holds $y$. Its squared norm $\|P_y v\|^2$ is the query magnitude of $y$ in $v$ (Bennett, Bernstein, Brassard and Vazirani, Definition 3.2), and also the probability that measuring the query register of a unit vector $v$ gives $y$.
