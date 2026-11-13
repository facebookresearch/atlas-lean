# Score of an alignment

Given a substitution score $\sigma$, which assigns an integer
$\sigma(a, b)$ to all letters $a, b \in \alpha$, and a gap score $g \in \mathbb{Z}$, the score of
an alignment $A$ over $\alpha$ is the sum, over all columns of $A$, of the score of the column
with respect to $\sigma$ and $g$.
