# Strict consensus of optimal gene tree rootings

Let $G_U$ be an unrooted binary gene tree with $n$ leaves, $S$ a rooted species tree, and fix duplication, transfer and loss costs. For a rooting $G_R$ of $G_U$ let $\mathrm{cost}(G_R, S)$ be the minimum DTL reconciliation cost, and let

$$\mathrm{OptRoot}(G_U, S) = \arg\min_{G_R \in \mathrm{Root}(G_U)} \mathrm{cost}(G_R, S)$$

be the set of optimal rootings ($G_U$ has $|E(G_U)|$ rootings). The **strict consensus** $SC$ of rooted trees on a common leaf set is the rooted tree whose clusters are exactly the clusters common to all of them. A **consensus reconciliation** consists of $SC$ for the trees in $\mathrm{OptRoot}(G_U, S)$ together with, for every internal node of $SC$, the distributions of its event type (speciation, duplication, transfer) and of its species-tree mapping over the optimal reconciliations of all optimal rootings.

**Lemma 1.** Every internal node of $SC$ other than its root is binary. Hence each subtree of $SC$ rooted at a non-root internal node has the same topology in every optimal rooting, and the reconciliation is summarized exactly on these conserved subtrees.

**Lemma 2.** If $G_U$ has $n$ leaves and $k$ distinct optimal rootings, then $SC$ has at most

$$(n - 1) - \lfloor k/2 \rfloor$$

internal nodes, and some placement of $k$ roots on $G_U$ attains this bound.

Optimal rootings are **maximally clustered** when the bound is attained. The plateau property known for reconciliation models without transfers, which keeps all optimal roots together, need not hold once transfers are allowed (as shown for host-symbiont cophylogeny), so the size of $SC$ measures how dispersed the optimal roots are.

## Expansion

Fix one optimal rooting $G_R^1$; the other optimal rootings are re-rootings on edges of $G_R^1$. Colour red the edges carrying another optimal root and every edge on the path from the root to such an edge. A subtree of $G_R^1$ containing only green edges appears unchanged in every optimal rooting, so its clusters survive in $SC$ and its nodes stay binary; a non-root node whose subtree contains a red edge loses its cluster in the rooting placed on that edge. Thus $SC$ has $(n-1) - r$ internal nodes, where $r$ counts non-root internal nodes whose subtree contains a red edge. Each such node has two child edges, so two extra roots can share one affected node, giving $r \ge \lfloor k/2 \rfloor$, with equality for a breadth-first placement of the roots just below the root of $G_R^1$.

## Sources

- S. Kundu, M. S. Bansal, "On the impact of uncertain gene tree rooting on duplication-transfer-loss reconciliation", BMC Bioinformatics 19(Suppl 9):290 (2018), Definitions 1-5, Lemmas 1 and 2, <https://doi.org/10.1186/s12859-018-2269-0>, PMCID PMC6101088.
