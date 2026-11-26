# Minimum duplication–loss reconciliation on a species network

**Setting.** Let $G$ be a binary gene tree and $N$ a rooted species network with $L(G)\subseteq L(N)$ (as in [best switching](best-switching-for-duplication-loss-reconciliation.md)). For nodes $x,y$ of $N$, $\mathcal M_N(x,y)$ is the set of speciation nodes $z$ having two *separated* paths to $x$ and $y$ (starting through different children of $z$); $\mathcal M\mathrm{in}_N(x,y)\subseteq\mathcal M_N(x,y)$ keeps those $z$ for which no other member lies on every path from $z$ to $x$ and $y$. A **reconciliation** $\alpha$ maps each gene node $u$ to a species node $\alpha_r(u)$ and an event $\alpha_e(u)\in\{\mathbb S,\mathbb D,\mathbb C\}$: leaves go to the leaf of their species ($\mathbb C$); a speciation requires $\alpha_r(u)\in\mathcal M_N(\alpha_r(u_1),\alpha_r(u_2))$; descendants of a duplication map at or below it, and descendants of any other node map strictly below it. With $\mathrm{dist}(x,y)$ the minimum number of speciation nodes on a path from $x$ down to $y$, losses at $u$ are $\min\{\mathrm{dist}(x_1,\alpha_r(u_1))+\mathrm{dist}(x_2,\alpha_r(u_2)),\ \mathrm{dist}(x_1,\alpha_r(u_2))+\mathrm{dist}(x_2,\alpha_r(u_1))\}$ for a speciation at $\alpha_r(u)$ with children $x_1,x_2$, and $\mathrm{dist}(\alpha_r(u),\alpha_r(u_1))+\mathrm{dist}(\alpha_r(u),\alpha_r(u_2))$ for a duplication. The cost is $\delta\,d(\alpha)+\lambda\,l(\alpha)$. Here a gene may follow any path in $N$, modelling recent hybridizations.

**Lemma 5 (normal form).** In a minimum-cost reconciliation (with no duplications on hybridization nodes), for every internal $u$ with children $u_1,u_2$:

1. if $\alpha_e(u)=\mathbb S$ then $\alpha_r(u)\in\mathcal M\mathrm{in}_N(\alpha_r(u_1),\alpha_r(u_2))$;
2. if $\alpha_e(u)=\mathbb D$ then the children's images are comparable and $\alpha_r(u)$ equals the higher of them.

**Theorem 3 (dynamic program).** Processing $G$ in post-order and storing, for each $u$, the set $\mathcal C(u)$ of pairs $(x,c)$ obtained by combining every pair of children's entries through all $x\in\mathcal M\mathrm{in}_N(y,z)$ (speciation) or the higher of $y,z$ when comparable (duplication), and keeping the cheapest cost per $x$, yields exactly the pairs such that some most parsimonious reconciliation of the subtree $G_u$ maps $u$ to $x$ with cost $c$.

**Theorem 4 (complexity).** If $N$ has $h$ hybridization nodes, the algorithm runs in $O(h^2\,|G|\,|N|)$ time; an optimal reconciliation is recovered by back-tracking from the cheapest entry of $\mathcal C(r(G))$.

## Depends on

- [Best switching for duplication–loss reconciliation](best-switching-for-duplication-loss-reconciliation.md)

## Expansion

Lemma 5 is an exchange argument: if a speciation sits above a node $y$ through which every path to both children's images passes, moving the mapping down to $y$ removes at least $2\,\mathrm{dist}(\alpha_r(u),y)$ losses below $u$ while adding at most $\mathrm{dist}(\alpha_r(u),y)$ at the parent; a duplication whose children's images are incomparable can likewise be turned into a cheaper speciation. Thus $|\mathcal C(u)|$ is bounded by the number of candidate mapping nodes, which is $O(h)$; each of the $O(h^2)$ child pairs costs two breadth-first searches, $O(|N|)$, to compute $\mathcal M\mathrm{in}_N$ and the distances.

## Sources

- T.-H. To, C. Scornavacca, "Efficient algorithms for reconciling gene trees and species networks via duplication and loss events", BMC Genomics 16(Suppl 10):S6 (2015), Definition 5 and the loss definition, Problem 2, Lemma 5, Algorithms 2–3, Theorems 3 and 4 (with Lemmas 6–7 bounding the candidate mappings), <https://doi.org/10.1186/1471-2164-16-S10-S6>, PMCID: PMC4603766.
