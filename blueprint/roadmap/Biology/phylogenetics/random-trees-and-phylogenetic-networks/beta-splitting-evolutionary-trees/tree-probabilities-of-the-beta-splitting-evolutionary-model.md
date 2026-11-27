# Tree probabilities of the Beta-splitting evolutionary model

Fix $\alpha, \beta > -1$. Let $B_1, B_2, \dots$ be i.i.d. $\mathrm{Beta}(\alpha + 1, \beta + 1)$ and $U_1, U_2, \dots$ i.i.d. uniform on $[0,1]$, independent of the $B_i$. Start with a single root labelled by the interval $[0,1]$, which records the diversification potential of the lineage. At step $i$, find the leaf whose interval $[a,b]$ contains $U_i$. Make it internal node $i$ and split it into a left leaf $[a, a + (b-a)B_i]$ and a right leaf $[a + (b-a)B_i, b]$. So sister species share their parent's potential in Beta-distributed, possibly asymmetric, proportions, and a lineage is chosen to speciate next with probability equal to its potential. After $n-1$ steps this gives a random **ranked planar binary tree** with $n$ leaves.

**Theorem.** For any unlabelled ranked planar binary tree $\tau$ with $n$ leaves, let $n_i^L$ and $n_i^R$ be the numbers of internal nodes in the left and right subtrees of internal node $i$. Then

$$
\mathbb{P}(\tau) = \prod_{i=1}^{n-1} \frac{1}{B(\alpha+1, \beta+1)} \int_0^1 b^{\,n_i^L + \alpha}(1 - b)^{\,n_i^R + \beta}\, db = \prod_{i=1}^{n-1} \frac{B(n_i^L + \alpha + 1,\ n_i^R + \beta + 1)}{B(\alpha + 1, \beta + 1)}.
$$

Forgetting the ranking, an (unranked) planar binary tree $\mathbf{t}$ with internal node set $\mathcal{I}(\mathbf{t})$ has probability

$$
\mathbb{P}(\mathbf{t}) = (n-1)! \prod_{i \in \mathcal{I}(\mathbf{t})} \frac{B(n_i^L + \alpha + 1,\ n_i^R + \beta + 1)}{(n_i^L + n_i^R + 1)\, B(\alpha + 1, \beta + 1)}.
$$

**Extinction and continuous time.** Adding freezing (extinction) events with probability $\delta$ per event gives a generating–organizing–deleting process. In the continuous-time version, each active leaf with potential $L_j$ splits at rate $\lambda(1-\delta)L_j$ and goes extinct at rate $\lambda\delta L_j$. Its embedded tree after $n$ events has the same law as the discrete process stopped after $n$ effective events.

## Depends on

- [Ranked labeled histories of coalescent trees](../../../coalescent-theory/ranked-labeled-histories-of-coalescent-trees/README.md)

## Expansion

Conditionally on the split proportions, the subsequent splits that fall into the left part of node $i$ are those with $U_j$ inside its left interval. Each such event has conditional probability proportional to $b_i$, so the $n_i^L$ left and $n_i^R$ right descendants of node $i$ contribute $b_i^{n_i^L}(1-b_i)^{n_i^R}$. Integrating each $b_i$ against the Beta density gives the product formula. Since the product does not depend on the ranking, summing over the rankings compatible with a planar shape multiplies it by the number of such rankings, $\prod_i \binom{n_i^L + n_i^R}{n_i^L}$, which rewrites as the factor $(n-1)!/\prod_i (n_i^L + n_i^R + 1)$. The construction generalizes the Blum–François Beta-splitting model and Aldous' Beta-splitting cladograms by letting the split of diversification potential between sister species be asymmetric.

## Sources

- Raazesh Sainudiin, Amandine Véber, "A Beta-splitting model for evolutionary trees", Royal Society Open Science 3 (2016), 160016, <https://doi.org/10.1098/rsos.160016>. Published version of arXiv:1511.08828, cited next; locators there refer to the arXiv version.
- Raazesh Sainudiin, Amandine Veber, "A Beta-splitting model for evolutionary trees", arXiv (2015). Section 2 (generating sequence and organizing map), Theorem 1, Lemma 1, Lemma 2. <https://doi.org/10.48550/arXiv.1511.08828>
