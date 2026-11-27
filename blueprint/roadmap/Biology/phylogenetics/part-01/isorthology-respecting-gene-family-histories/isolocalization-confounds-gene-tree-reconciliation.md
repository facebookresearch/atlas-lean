# Isolocalization confounds gene tree reconciliation

A **history** $H$ of a gene family is a rooted tree whose internal nodes are speciations or duplications and whose leaves are extant genes or losses. Genes $a, b$ are **orthologous** if $\mathrm{lca}_H(a,b)$ is a speciation and **paralogous** if it is a duplication. Assume that after each duplication exactly one copy (the **retainer**) keeps the parental function and the other (the **mutant**) does not. Two orthologs are **isorthologous** if both kept the function of their LCA; an **isorthogroup** is a maximal set of pairwise isorthologous genes. A duplication node $d$ **survives** if $d = \mathrm{lca}_H(a,b)$ for some extant $a,b$; a speciation node $s$ survives if $s = \mathrm{lca}_H(a_1,a_2)$ for some isorthologous pair.

A gene tree $G$ has the **isolocalization property** if for every isorthologous pair $a_1, a_2$, the leaves below $\mathrm{lca}_G(a_1,a_2)$ are all isorthologous to $a_1$ and $a_2$; this is what slower, constrained evolution of functional copies tends to produce in a well-supported tree.

**Theorem.** If $H$ has a surviving duplication node descending from a surviving speciation node, then $H$ with its loss leaves removed is not a gene tree with the isolocalization property.

**Corollary 1.** A gene tree with the isolocalization property never yields, by reconciliation with the species tree, a history equivalent to a true history $H$ containing a surviving duplication below a surviving speciation.

**Corollary 2.** The same holds when only a subtree $G'$ of the gene tree has the isolocalization property, provided $H$ has a speciation $s$ with surviving pair $(a_1,a_2)$ and a descendant duplication $d$ with surviving pair $(a_2, b)$, all three genes in $G'$.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Take isorthologs $a_1, a_2$ with $\mathrm{lca}_H(a_1,a_2) = s$ and a gene $b$ with $\mathrm{lca}_H(a_2, b) = d$ below $s$. Then $b$ is orthologous but not isorthologous to $a_1$, yet lies in the subtree rooted at $s$, violating isolocalization. Since a reconciliation is the gene tree itself with nodes labelled by the LCA mapping, it can only return a history whose topology is that of $G$; so the true $H$ is unreachable. In the smallest example, reconciliation moves the duplication to the root and invents a loss absent from the true history; the problem is not merely misrooting.

## Sources

- K. M. Swenson and N. El-Mabrouk, "Gene trees and species trees: irreconcilable differences", BMC Bioinformatics 13 (Suppl 19) (2012), S15, Definitions 1–5, Hypothesis 1, Theorem 1 and Corollaries 1–2, <https://doi.org/10.1186/1471-2105-13-S19-S15>, PMCID: PMC3526438.
