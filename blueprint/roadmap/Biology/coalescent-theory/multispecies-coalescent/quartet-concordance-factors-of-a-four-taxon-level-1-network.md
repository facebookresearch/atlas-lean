# Quartet concordance factors of a four-taxon level-1 network

For taxa $\{a, b, c, d\}$ the three unrooted quartets are $q_1 = ab|cd$, $q_2 = ac|bd$ and $q_3 = ad|bc$. The **concordance factor** $\mathrm{CF}_{q}$ of a quartet is the probability that a gene tree drawn under [the network multispecies coalescent](network-multispecies-coalescent-fixed-network-ge.md) displays $q$. Branch lengths are in coalescent units and $\gamma$ is the inheritance probability of a hybrid edge.

**Species tree (no reticulation).** If the unrooted species quartet is $ab|cd$ with internal branch length $t$, then

$$(\mathrm{CF}_{ab|cd}, \mathrm{CF}_{ac|bd}, \mathrm{CF}_{ad|bc}) = \Big(1 - \tfrac23 e^{-t},\ \tfrac13 e^{-t},\ \tfrac13 e^{-t}\Big),$$

independent of the root.

**One reticulation with one hybrid descendant.** Suppose a gene from the hybrid taxon $c$ follows a hybrid edge sister to $d$ with probability $\gamma$, and otherwise the tree edge sister to $(ab)$, and the two displayed unrooted trees are both $ab|cd$, with internal lengths $t_1$ and $t_1 + t_2$. Then the CFs are the $\gamma$-mixture of the two tree CFs:

$$\mathrm{CF}_{ab|cd} = (1-\gamma)\big(1 - \tfrac23 e^{-t_1}\big) + \gamma\big(1 - \tfrac23 e^{-t_1 - t_2}\big), \qquad \mathrm{CF}_{ac|bd} = \mathrm{CF}_{ad|bc} = \tfrac13\big((1-\gamma)e^{-t_1} + \gamma e^{-t_1 - t_2}\big).$$

This network has the same CFs as the species tree $ab|cd$ with internal length

$$t_3 = -\log\big((1-\gamma)e^{-t_1} + \gamma e^{-t_1 - t_2}\big),$$

so its reticulation cannot be detected from the quartet CFs of these four taxa.

**One reticulation with two hybrid descendants.** If the hybrid node has descendants $A$ and $B$, joined above it by a branch of length $t_1$, and the two lineages pick their parent edges independently, then

$$\mathrm{CF}_{AB|CD} = 1 - e^{-t_1} + e^{-t_1}\Big[(1-\gamma)^2\big(1 - \tfrac23 e^{-t_2 - t_3}\big) + 2\gamma(1-\gamma)\big(1 - \tfrac23 e^{-t_2}\big) + \gamma^2\big(1 - \tfrac23 e^{-t_4 - t_2}\big)\Big],$$

a mixture over the four routings of the two lineages. The labels $t_2, t_3, t_4$ are the branch lengths of the paper's Figure 3.

**Several reticulations.** On a level-1 network the reticulation cycles share no edges. Each cycle can be replaced, recursively, by a four-taxon network with at most one reticulation and transformed branch lengths, without changing the CFs. Since every displayed tree's CFs are root-independent, so are the network CFs.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [The multispecies coalescent](gene-tree-prob.md)

## Expansion

Conditioned on which parent edge each hybrid lineage takes, the gene tree evolves under the multispecies coalescent on a displayed species tree, and the tree formula applies. Two lineages on the internal edge fail to coalesce with probability $e^{-t}$, after which all three resolutions are equally likely; this gives the tree CFs. Averaging over routings with weights $\gamma$ and $1 - \gamma$ per lineage gives the mixtures. With two hybrid descendants, they may coalesce below the hybrid node (probability $1 - e^{-t_1}$), which yields $AB|CD$ outright. The equivalent-tree length $t_3$ solves $\tfrac13 e^{-t_3} = \mathrm{CF}_{ac|bd}$; the major CF then agrees automatically because the three CFs sum to $1$.

## Sources

- C. Solís-Lemus and C. Ané, "Inferring phylogenetic networks with maximum pseudolikelihood under incomplete lineage sorting", *PLoS Genetics* 12(3) (2016), e1005896, <https://doi.org/10.1371/journal.pgen.1005896> (PMC4780787), Models section, subsections "Pseudolikelihood on a network" and "Quartet CF for a 4-taxon network under ILS" (Figures 2–3), with the remaining four-taxon cases in S1 Text.
