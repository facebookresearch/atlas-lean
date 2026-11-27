# Quartet summary methods can return a tree not displayed by a level-1 network

**Network multispecies coalescent.** In a phylogenetic network with a single $n$-cycle and hybridization parameter $\gamma$, the distribution of gene trees is the $(\gamma, 1-\gamma)$ mixture of the multispecies-coalescent distributions on the two displayed trees obtained by deleting one hybrid edge. For the four-taxon 4-cycle network with displayed quartet trees $AB|CD$ (weight $1-\gamma$, internal length $x$) and $AD|BC$ (weight $\gamma$, internal length $y$),

$$P(AB|CD) = (1-\gamma)\big(1 - \tfrac23 e^{-x}\big) + \gamma\,\tfrac13 e^{-y},\quad P(AD|BC) = (1-\gamma)\,\tfrac13 e^{-x} + \gamma\big(1 - \tfrac23 e^{-y}\big),$$

$$P(AC|BD) = (1-\gamma)\,\tfrac13 e^{-x} + \gamma\,\tfrac13 e^{-y},\qquad P(AB|CD) - P(AD|BC) = (1-\gamma)(1 - e^{-x}) - \gamma(1 - e^{-y}).$$

**Expected quartet score.** A quartet summary method (ASTRAL) seeks the unrooted tree $T$ maximizing the number of gene-tree quartets it agrees with; with infinitely many error-free gene trees this is the expected score $A(T) = \sum_{q \in \mathcal{Q}(T)} P(q)$.

**Theorem.** Let $N$ be the semidirected five-taxon network whose 5-cycle consists of a hybrid node with child $C$, a parent $g$ adjacent to leaf $B$ and a parent $j$ adjacent to leaf $D$, and the path $g \overset{e_4}{-} a \overset{e_3}{-} e \overset{e_2}{-} j$ through the attachment points $a$ of leaf $A$ and $e$ of leaf $E$. The hybrid edge from $g$ has inheritance probability $\gamma$ and the one from $j$ has $1-\gamma$, so the displayed trees are $T_1 = ((B,C),A,(D,E))$ and $T_2 = ((A,B),E,(C,D))$. Put $y_i = e^{-e_i}$. If

$$(1 - y_2) > \frac{\gamma}{1-\gamma}\,(1 - y_3 y_4) \quad\text{and}\quad (1 - y_3) < \min\Big(\frac{\gamma}{2-\gamma}(1 - y_4),\ \frac{1-\gamma}{1+\gamma}(1 - y_2)\Big),$$

then under the network multispecies coalescent the tree $S = (((A,E),B),C,D)$, which is not displayed by $N$, has strictly larger expected quartet score than both $T_1$ and $T_2$. By symmetry, the mirror conditions make $S' = (((A,E),D),C,B)$ beat both displayed trees. Five-cycle networks are not quartet-anomalous, so this happens even though every quartet's most probable gene tree is displayed by $N$; the result extends to any network containing a $k$-cycle with $k \ge 5$.

## Depends on

- [Multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/README.md)
- [Quartet support and determination of trees by quartets](../../quartet-support-and-determination-of-trees-by-qu/README.md)

## Expansion

The two conditions fix, for each of the five four-taxon subsets, which quartet topology is most probable: $AB|CD$, $AE|CD$, $BE|CD$, $AE|BC$ and $AB|DE$. No single tree displays all five, so every tree loses the gap between the best and runner-up quartet on at least one subset. $T_2$ misses only $\{A,B,C,E\}$, losing $\gamma(1-y_4) - (1-\gamma)(1-y_3)$; $T_1$ misses $\{A,C,D,E\}$ among others, losing at least $(1-\gamma)(1-y_2) - \gamma(1-y_3)$; $S$ misses only $\{A,B,D,E\}$, whose subnetwork is a tree with internal branch $e_3$, losing $1 - y_3$. The second condition makes $S$'s single loss the smallest. Simulations with $e_2 = 2$, $e_3 = 0.2$, $e_4 = 1.1$, $\gamma = 0.5$ and $10^5$ gene trees indeed returned $S$; about 6% of parameter draws with exponential edge lengths satisfy the hypotheses.

## Sources

- V. Dinh, H. Baños, "Misspecification strikes: ASTRAL can mislead in the presence of hybridization, even for nonanomalous scenarios", Molecular Biology and Evolution 42(3) (2025) msaf049, Equations (1)–(7), Theorem 1 and Corollary 2, <https://doi.org/10.1093/molbev/msaf049>, PMCID PMC11934270.
