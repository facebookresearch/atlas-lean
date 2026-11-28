# Independent-sites likelihood selects the majority site pattern

**Setting.** Three species $A, B, C$ with one sequence each evolve under the multispecies coalescent with a molecular clock and the Jukes–Cantor substitution model. The three possible rooted species trees are $S_1 = ((A,B),C)$, $S_2 = ((B,C),A)$ and $S_3 = ((C,A),B)$. At each of $m$ loci of $n$ sites, the data are the counts $x_{ij}$ of the five site patterns $j = 0, \dots, 4$: $xxx$, $xxy$, $yxx$, $xyx$, $xyz$ (for distinct nucleotides $x, y, z$; pattern $xxy$ means $A$ and $B$ agree). Let $x_{\cdot j} = \sum_i x_{ij}$ be the counts pooled across loci. The *independent-sites maximum likelihood* method (isml, coalescent-aware concatenation) treats every site as an independent draw from the marginal site-pattern distribution $\bar p_j(S, \theta)$, obtained by averaging the pattern probabilities over the coalescent distribution of gene trees and times, and maximizes $\prod_j \bar p_j(S, \theta)^{x_{\cdot j}}$ over $S$ and parameters $\theta$.

**Theorem.**

1. If the true species tree is $S_1$ with parameters $\theta_1$, then $\bar p_1 > \bar p_2 = \bar p_3$.
2. Isml infers $S_1$ if $x_{\cdot 1} > \max\{x_{\cdot 2}, x_{\cdot 3}\}$, and symmetrically for $S_2, S_3$.

Hence isml chooses the same species tree as maximum-likelihood concatenation whenever one pooled count among $x_{\cdot 1}, x_{\cdot 2}, x_{\cdot 3}$ is strictly largest, since concatenation also selects $G_1$ if $x_{\cdot 1} > \max(x_{\cdot 2}, x_{\cdot 3})$, and it is statistically consistent as $m \to \infty$ without needing parameter estimates.

## Depends on

- [Jukes–Cantor transition probability](../../../phylogenetics/jukes-cantor-model/jc-prob.md)
- [The multispecies coalescent](../gene-tree-prob.md)
- [Rooted binary species tree with branch lengths](../species-tree.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

(1) The marginal probabilities average over four gene-tree classes: the gene tree $((A,B),C)$ formed after the $AB$ speciation, and three equiprobable topologies formed in the ancestral population. The three ancestral topologies contribute equally to $xxy$, $yxx$ and $xyx$, while the first one strictly favours $xxy$. (2) If $x_{\cdot 1} > x_{\cdot 2}$, swapping the roles of patterns $1$ and $2$ maps the maximized likelihood under $S_2$ to a likelihood under $S_1$ that is at least as large, because $q_1^{x_{\cdot1}} q_2^{x_{\cdot2}} > q_1^{x_{\cdot2}} q_2^{x_{\cdot1}}$ whenever $q_1 > q_2 > 0$.

## Sources

- T. Zhu and Z. Yang, "Complexity of the simplest species tree problem", *Molecular Biology and Evolution* (2021), Theorem 3 and the sections on concatenation and isml. <https://doi.org/10.1093/molbev/msab009> (PMC8382899)
