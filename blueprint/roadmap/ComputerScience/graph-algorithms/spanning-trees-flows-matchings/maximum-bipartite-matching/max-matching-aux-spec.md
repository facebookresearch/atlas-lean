# Enough augmentations reach a maximum matching

In a bipartite graph with right vertices
$0, \dots, b-1$, let $\mu$ be a valid partner array (it assigns to each right vertex at most one
left partner, partners are neighbours, and no left vertex is the partner of two right vertices).
Let $f \in \mathbb{N}$ satisfy $b < |\mathrm{matched}(\mu)| + f$, where $\mathrm{matched}(\mu)$ is
the set of right vertices with a partner, and let $\mu'$ be the result of the augmentation loop
from $\mu$ with fuel $f$. Then $\mu'$ is valid, and every matching $M$ of the graph satisfies
$|M| \le |\mathrm{pairs}(\mu')|$, where $\mathrm{pairs}(\mu')$ is the set of pairs $(i, j)$ with
$\mu'(j) = i$.
